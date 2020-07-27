import json
import pickle
from util import compute_edits 
from base_client import BaseClient, IntegrityError
from crypto import CryptoError


#def string_concat(*strings_to_join):
 #   return '|'.join(strings_to_join)

#lets get the merkle tree
class Node(object):
    """Each node has references to left and right child nodes, parent, and sibling.
    It can also be aware of whether it is on the left or right hand side. data is hashed
    automatically by default, but does not have to be, if prehashed param is set to False.
    """
    def __init__(self, data, pos):
        self.val = data
        self.l = None
        self.r = None
        self.p = None
        self.sib = None
        self.side = None
        self.pos = pos

        


    def __repr__(self):
        return "Val: <" + str(self.val) + ">"

    def traverse(self, clients, file_id, row, col):
        temp_name = clients.crypto.cryptographic_hash(file_id + "temp_name" , 'SHA256')
        clients.storage_server.put(temp_name + str(row) + "-" + str(col), self.val)
        if self.l is not None:
            self.l.traverse(clients, file_id, row+1, col*2)
        if self.r is not None:
            self.r.traverse(clients, file_id, row+1, col*2+1)

    def tr_compare(self, new_clients, file_id, row, col):
        temp_name = new_clients.crypto.cryptographic_hash(file_id + "temp_name" , 'SHA256')
        val = new_clients.storage_server.get(temp_name+ str(row) + "-" + str(col))
        if val is None or val != self.val:
            new_clients.storage_server.put(temp_name + str(row) + "-" + str(col), self.val)
            #now we need to consider the child's case
            if self.l is None and self.r is None:
                return [self.pos]
            if self.l is not None:
                return self.l.tr_compare(new_clients, file_id, row+1, col*2)
            if self.r is not None:
                return self.r.tr_compare(new_clients, file_id, row+1, col*2+1)
            

        else:
            return []






    def tr_download(self, new_clients,file_id, row, col, result_list):
        temp_name = new_clients.crypto.cryptographic_hash(file_id + "temp_name" , 'SHA256')
        val = new_clients.storage_server.get(temp_name+ str(row) + "-" + str(col))
        # no guanruntee that val exsits
        if val is None:
            return []
        elif self.val != val:
            #if not the same
            if self.l is None and self.r is None:
                return [self.pos]
            if self.l is not None:
                left_list = self.l.tr_download(new_clients, file_id, row+1, col*2, result_list)
            if self.r is not None:
                right_list = self.r.tr_download(new_clients, file_id, row+1, col*2+1, result_list)
            result_list = left_list + right_list
            return result_list
        else:
            return []

    def tr_mod(self, new_clients, file_id, row, col, list_of_node):
        temp_name = new_clients.crypto.cryptographic_hash(file_id + "temp_name" , 'SHA256')
        new_clients.storage_server.put(temp_name + str(row) + "-" + str(col), list_of_node[0][0])
        if len(list_of_node) > 1:
            if list_of_node[0][1] == 'R':
                self.r.tr_mod(new_clients, file_id, row+1, col*2 + 1, list_of_node[1:])
            elif list_of_node[0][1] == 'L':
                self.l.tr_mod(new_clients, file_id, row+1, col*2 , list_of_node[1:])
            elif list_of_node[0][1] == 'SELF':
                return 
        else:
            return













class MerkleTree(object):
    """A Merkle tree implementation.  Added values are stored in a list until the tree is built.
    A list of data elements for Node values can be optionally supplied.  Data supplied to the
    constructor is hashed by default, but this can be overridden by providing prehashed=False
    in which case, node values should be supplied in hex format.
    """
    def __init__(self, leaves, myclient, file_name):
        self.leaves= []
        index = 0
        for leaf in leaves:
            self.leaves.append(Node(leaf, index))
            index = index +1
        self.root = None
        self.client = myclient
        self.file_name  = file_name

    def __eq__(self, obj):
        return (self.root.val == obj.root.val) and (self.__class__ == obj.__class__)

    def add(self, data):
        """Add a Node to the tree, providing data, which is hashed automatically
        """
        self.leaves.append(Node(data, -1))

    def clear(self):
        """Releases the Merkle root, and node references are garbage collected
        """
        self.root = None

    def build(self):
        """Calculate the merkle root and make references between nodes in the tree.
        """
        if not self.leaves:
            raise AssertionError('No leaves')
        layer = self.leaves[::]
        while 1:
            index = 0
            for elem in layer:
                temp_name = self.client.crypto.cryptographic_hash(self.client.username + self.file_name , 'SHA256')
                self.client.storage_server.put(temp_name+ str(len(layer)) + "-" + str(index), elem.val)
                index = index +1
            layer = self._build(layer)
            if len(layer) == 1:
                self.root = layer[0]
                temp_name = self.client.crypto.cryptographic_hash(self.client.username + self.file_name, 'SHA256')
                self.client.storage_server.put(temp_name+ str(1) + "-" + str(0), self.root.val)
                break
        return self.root.val

    def pre_build(self):
        """Calculate the merkle root and make references between nodes in the tree.
        """
        if not self.leaves:
            raise AssertionError('No leaves')
        layer = self.leaves[::]
        while 1:
            layer = self._build(layer)
            if len(layer) == 1:
                self.root = layer[0]
                break
        return self.root.val

    def _build(self, leaves):
        """Private helper function to create the next aggregation level and put all references in place
        """
        new, odd = [], None
        # ensure even number of leaves
        if len(leaves) % 2 == 1:
            odd = leaves.pop(-1)
        for i in range(0, len(leaves), 2):
            newnode = Node(self.client.crypto.cryptographic_hash(leaves[i].val + leaves[i + 1].val, 'SHA256'), -1)
            newnode.l, newnode.r = leaves[i], leaves[i + 1]
            leaves[i].side, leaves[i + 1].side, leaves[i].p, leaves[i + 1].p = 'L', 'R', newnode, newnode
            leaves[i].sib, leaves[i + 1].sib = leaves[i + 1], leaves[i]
            new.append(newnode)
        if odd:
            new.append(odd)
        return new

    def get_chain(self, index):
        """Assemble and return the chain leading from a given node to the merkle root of this tree
        """
        chain = []
        this = self.leaves[index]
        chain.append((this.val , 'SELF'))
        while 1:
            if not this.p:
                break
            else:
                chain.append((this.p.val, this.side))
                this = this.p
        return chain[::-1]

    def get_all_chains(self):
        """Assemble and return chains for all nodes to the merkle root
        """
        return [self.get_chain(i) for i in range(len(self.leaves))]

    def get_hex_chain(self, index):
        """Assemble and return the chain leading from a given node to the merkle root of this tree
        with hash values in hex form
        """
        return [(i[0].encode('hex'), i[1]) for i in self.get_chain(index)]

    def get_all_hex_chains(self):
        """Assemble and return chains for all nodes to the merkle root, in hex form
        """
        return [[(i[0].encode('hex'), i[1]) for i in j] for j in self.get_all_chains()]

    def traverse_upload(self, file_id):
        #we want to traverse the tree and then upload the nodes
        if self.root is None:
            return None
        self.root.traverse(self.client, file_id,  0, 0)

    def traverse_compare(self, file_id):
        if self.root is None:
            return None
        result_list = []
        result_list = self.root.tr_compare(self.client, file_id, 0, 0)
        return result_list

    def traverse_download(self, file_id):
        if self.root is None:
            return None
        result_list = []
        result_list = self.root.tr_download(self.client, file_id, 0, 0, result_list)
        return result_list

    def modified(self, file_id, index):
        if self.root is None:
            return None
        list_of_node = self.get_chain(index)
        self.root.tr_mod(self.client, file_id, 0, 0, list_of_node)




def check_chain(chain):
    """Verify a presented merkle chain to see if the Merkle root can be reproduced.
    """
    link = chain[0][0]
    for i in range(1, len(chain) - 1):
        if chain[i][1] == 'R':
            link = hash_function(link + chain[i][0]).digest()
        elif chain[i][1] == 'L':
            link = hash_function(chain[i][0] + link).digest()
    if link == chain[-1][0]:
        return link
    else:
        raise AssertionError('The Merkle Chain is not valid')


def check_hex_chain(chain):
    """Verify a merkle chain, presented in hex form to see if the Merkle root can be reproduced.
    """
    return check_chain([(i[0].decode('hex'), i[1]) for i in chain]).encode('hex')



def join_chains(low, high):
    """Join two hierarchical merkle chains in the case where the root of a lower tree is an input
    to a higher level tree. The resulting chain should check out using the check functions.
    """
    return low[:-1] + high[1:]








class Client(BaseClient):
    def __init__(self, storage_server, public_key_server, crypto_object,
                 username):
        super().__init__(storage_server, public_key_server, crypto_object,
                         username)
        helper = self.string_concat(self.username, 'hello_world')
        uid = self.crypto.cryptographic_hash(helper, 'SHA256')
        helper2 = self.string_concat(self.username, 'dictionary')
        uid2 = self.crypto.cryptographic_hash(helper2, 'SHA256')
        if self.storage_server.get(uid) is None:
            #have no dictionary yet, and has no key for that dictionary yet
            self.dictionary = {}
            input_string = json.dumps(self.dictionary)
            God_key = self.crypto.get_random_bytes(16)
            encrypted_God_key= self.crypto.asymmetric_encrypt(God_key, self.pks.get_encryption_key(self.username))

            signed_God_key = self.crypto.asymmetric_sign(encrypted_God_key, self.rsa_priv_key)
            self.storage_server.put(uid, signed_God_key+encrypted_God_key)
            #let encrypt the dictionary now
            IV = self.crypto.get_random_bytes(16)
            encry_dictionary =IV+ self.crypto.symmetric_encrypt(input_string, self.crypto.cryptographic_hash(God_key,'SHA256'), 'AES','CBC', IV, None,self.crypto.new_counter(128),None, 128)
            encry_dictionary_mac = self.crypto.message_authentication_code(encry_dictionary, self.crypto.cryptographic_hash(God_key+ "Dictionary_mac", 'SHA256'), 'SHA256')
            self.storage_server.put(uid2, encry_dictionary_mac+encry_dictionary)
     
        else:
            #To get the storage key
            total_key = self.storage_server.get(uid)
            signed_God_key = total_key[:512]
            encrypted_God_key = total_key[512:]
            if not self.crypto.asymmetric_verify(encrypted_God_key, signed_God_key, self.pks.get_signature_key(self.username)):
                raise IntegrityError()
            God_key = self.crypto.asymmetric_decrypt(encrypted_God_key, self.elg_priv_key)
            #Stoarge key obtained

            if self.storage_server.get(uid2) is None:
                dictionary = {}
                self.dictionary = dictionary
                input_string = json.dumps(dictionary)
                IV = self.crypto.get_random_bytes(16)
                encry_dictionary = IV + self.crypto.symmetric_encrypt(input_string, self.crypto.cryptographic_hash(God_key, 'SHA256'), 'AES','CBC',IV, None,self.crypto.new_counter(128),None, 128)
                encry_dictionary_mac = self.crypto.message_authentication_code(encry_dictionary, self.crypto.cryptographic_hash(God_key+ "Dictionary_mac"), 'SHA256')
                self.storage_server.put(uid2, encry_dictionary_mac+encry_dictionary)
            else:
                total_dictionary = self.storage_server.get(uid2)
                encry_dictionary_mac = total_dictionary[:64]
                encry_dictionary = total_dictionary[64:]
                IV = encry_dictionary[:32]
                if self.crypto.message_authentication_code(encry_dictionary,self.crypto.cryptographic_hash(God_key+ "Dictionary_mac",'SHA256'),'SHA256') !=encry_dictionary_mac :
                    raise IntegrityError()
                input_string = self.crypto.symmetric_decrypt(encry_dictionary[32:],self.crypto.cryptographic_hash(God_key,'SHA256'), 'AES','CBC',IV, None,self.crypto.new_counter(128),None, 128)
                dictionary = json.loads(input_string)
                self.dictionary = dictionary
        #need a sharing key dictionary
        #meaning we are not store anything when we init
        self.stored_file = {}
        self.cipher_text_list = {}
        self.shared_dictionary= {}

            

            

        






    def string_concat(self,*strings_to_join):
        return '|'.join(strings_to_join)
    def upload(self, name, value):
        """Upload a certain file by user with username and value. Encrypt the file along the way"""
        helper = self.string_concat(self.username, 'hello_world')
        uid = self.crypto.cryptographic_hash(helper, 'SHA256')
        helper2 = self.string_concat(self.username, 'dictionary')
        uid2 = self.crypto.cryptographic_hash(helper2, 'SHA256')
        helper3 = self.string_concat(self.username, 'sharing_dictionary')
        uid3 =self.crypto.cryptographic_hash(helper3,'SHA256')
        total_key = self.storage_server.get(uid)
        if total_key is None:
            dictionary = {}
            input_string = json.dumps(dictionary)
            God_key = self.crypto.get_random_bytes(16)
            encrypted_God_key= self.crypto.asymmetric_encrypt(God_key, self.pks.get_encryption_key(self.username))
            signed_God_key = self.crypto.asymmetric_sign(encrypted_God_key, self.rsa_priv_key)
            self.storage_server.put(uid, signed_God_key+encrypted_God_key)
            IV = self.crypto.get_random_bytes(16)
            encry_dictionary = IV+self.crypto.symmetric_encrypt(input_string, self.crypto.cryptographic_hash(God_key,'SHA256'), 'AES','CBC', IV, None,None,None, 128)
            encry_dictionary_mac = self.crypto.message_authentication_code(encry_dictionary, self.crypto.cryptographic_hash(God_key + 'Dictionary_mac','SHA256'), 'SHA256')
            self.storage_server.put(uid2, encry_dictionary_mac+encry_dictionary)

        else:
            signed_God_key = total_key[:512]
            encrypted_God_key = total_key[512:]
            if not self.crypto.asymmetric_verify(encrypted_God_key, signed_God_key, self.pks.get_signature_key(self.username)):
                raise IntegrityError()
            God_key = self.crypto.asymmetric_decrypt(encrypted_God_key, self.elg_priv_key)
            total_dictionary = self.storage_server.get(uid2)
            if total_dictionary is None:
                dictionary = {}
                self.dictionary = dictionary
                input_string = json.dumps(dictionary)
                IV = self.crypto.get_random_bytes(16)
                encry_dictionary =IV + self.crypto.symmetric_encrypt(input_string, self.crypto.cryptographic_hash(God_key,'SHA256'), 'AES','CBC',IV, None,None,None, 128)
                encry_dictionary_mac = self.crypto.message_authentication_code(encry_dictionary, self.crypto.cryptographic_hash(God_key+ 'Dictionary_mac','SHA256'), 'SHA256')
                self.storage_server.put(uid2, encry_dictionary_mac+encry_dictionary)
            else:
                encry_dictionary_mac = total_dictionary[:64]
                encry_dictionary = total_dictionary[64:]
                if self.crypto.message_authentication_code(encry_dictionary,self.crypto.cryptographic_hash(God_key +'Dictionary_mac','SHA256'),'SHA256') !=encry_dictionary_mac :
                    raise IntegrityError()
                IV = encry_dictionary[:32]
                input_string = self.crypto.symmetric_decrypt(encry_dictionary[32:],self.crypto.cryptographic_hash(God_key,'SHA256'), 'AES','CBC',IV, None,None,None, 128)
                dictionary = json.loads(input_string)
                self.dictionary = dictionary


        if self.shared_dictionary is None:
            total_shared_dictionary = self.storage_server.get(uid3)
            if total_shared_dictionary is None:
                self.shared_dictionary= {}
                shared_dictionary_string = json.dumps(self.shared_dictionary)
                IV = self.crypto.get_random_bytes(16)
                encry_shared_dictionary = IV+ self.crypto.symmetric_encrypt(shared_dictionary_string, self.crypto.cryptographic_hash(God_key + "shared_dictionary",'SHA256'), 'AES','CBC',IV, None,None,None, 128)
                encry_shared_dictionary_mac = self.crypto.message_authentication_code(encry_shared_dictionary, self.crypto.cryptographic_hash(God_key + "shared_dictionary_mac",'SHA256'), 'SHA256')
                self.storage_server.put(uid3, encry_shared_dictionary_mac+encry_shared_dictionary)
            else:
                encry_shared_dictionary = total_shared_dictionary[64:]
                encry_shared_dictionary_mac = total_shared_dictionary[:64]
                IV = encry_shared_dictionary[:32]
                if self.crypto.message_authentication_code(encry_shared_dictionary,self.crypto.cryptographic_hash(God_key+"shared_dictionary_mac",'SHA256'),'SHA256') != encry_shared_dictionary_mac :
                    raise IntegrityError()
                shared_dictionary_string = self.crypto.symmetric_decrypt(encry_shared_dictionary[32:],self.crypto.cryptographic_hash(God_key+"shared_dictionary",'SHA256'), 'AES','CBC',IV, None,None,None, 128)
                self.shared_dictionary = json.loads(shared_dictionary_string)
        file_id = None
        file_key = None

        if name in self.dictionary :
            current_key = self.dictionary[name]
            file_id = current_key[:8]
            file_key = current_key[8:]
        elif name in self.shared_dictionary:
            current_key =self.shared_dictionary[name]
            key_a_to_b = current_key [:16]
            id_a_to_b = current_key[16:]
            total_shared_key = self.storage_server.get(self.crypto.cryptographic_hash(id_a_to_b,'SHA256'))
            if not total_shared_key is None:
               mac_shared_key = total_shared_key[:64]
               encrypt_shared_key = total_shared_key[64:]
               IV = encrypt_shared_key[:32]
               if self.crypto.message_authentication_code(encrypt_shared_key+self.crypto.cryptographic_hash(id_a_to_b,'SHA256'), self.crypto.cryptographic_hash(key_a_to_b + "key_ab_mac", 'SHA256'), 'SHA256') != mac_shared_key:
                   raise IntegrityError()
               file_id_key = self.crypto.symmetric_decrypt(encrypt_shared_key[32:], self.crypto.cryptographic_hash(key_a_to_b,'SHA256'),'AES','CBC',IV, None,self.crypto.new_counter(128),None, 128)
               file_id = file_id_key[:8]
               file_key = file_id_key[8:]
        if file_id is None:
            file_id = self.crypto.get_random_bytes(4)
            file_key = self.crypto.get_random_bytes(4)
            dictionary[name] = file_id + file_key
        new_dict_string = json.dumps(dictionary)
        IV = self.crypto.get_random_bytes(16)
        new_dict_cipher = IV+ self.crypto.symmetric_encrypt(new_dict_string, self.crypto.cryptographic_hash(God_key,'SHA256'), 'AES','CBC',IV, None,None,None, 128)
        new_dict_mac = self.crypto.message_authentication_code(new_dict_cipher, self.crypto.cryptographic_hash(God_key + "Dictionary_mac",'SHA256'), 'SHA256')
        self.storage_server.put(uid2, new_dict_mac+new_dict_cipher)

        mac_key = self.crypto.cryptographic_hash(file_id+ "hello_world" , 'SHA256')
        encryption_key = self.crypto.cryptographic_hash(file_key,'SHA256')

        if self.stored_file is None:
            self.upload_helper1(name, file_id, mac_key, encryption_key, value)
        elif name not in self.stored_file:
            self.upload_helper1(name, file_id, mac_key, encryption_key, value)
        else:
            old_version = self.stored_file[name]
            if len(old_version) != len(value):
                self.upload_helper1(name, file_id, mac_key, encryption_key, value)
            else:
                different_list = compute_edits(old_version, value)
                self.upload_helper2(name, file_id, mac_key, encryption_key, value, old_version, different_list)
           
    def upload_helper1(self, name, file_id, file_mac_key, file_encryption_key, value):
        #let us use this normal implementation of upload, such as the not efficient one, the normal one
        self.stored_file[name] = value
        split_list = [value[i:i+32] for i in range(0, len(value), 32)]
        self.cipher_text_list[name] = []
        for elem in split_list:
            IV = self.crypto.get_random_bytes(8)
            cipher_text = IV+self.crypto.symmetric_encrypt(elem, file_encryption_key, 'AES', 'CBC', IV*2 , None, None, None, 128)
            self.cipher_text_list[name].append(cipher_text)
        hash_list = []
        for elem in self.cipher_text_list[name]:
            hash_list.append(self.crypto.cryptographic_hash(elem, 'SHA256'))

        temp_mT = MerkleTree(hash_list,self, name)
        temp_mT.pre_build()
        temp_mT.traverse_upload(file_id)
        mac_text = self.crypto.message_authentication_code(temp_mT.root.val, file_mac_key, 'SHA256')
        self.storage_server.put(file_id +self.crypto.cryptographic_hash("mac", 'SHA256'), mac_text + str(len(self.cipher_text_list[name])))
        index = 0
        for elem in self.cipher_text_list[name]:
            self.storage_server.put(file_id + str(index), elem)
            index = index + 1





    def upload_helper2(self, name, file_id, file_mac_key, file_encryption_key, value, old_version, different_list):
        
        self.stored_file[name] = value
        total_length = len(old_version)
        if name not in self.cipher_text_list:
            self.upload_helper1(name, file_id, file_mac_key, file_encryption_key, value)


        hash_list = []
        for elem in self.cipher_text_list[name]:
            hash_list.append(self.crypto.cryptographic_hash(elem, 'SHA256'))
        old_temp_tree = MerkleTree(hash_list, self, name)

        old_temp_tree.pre_build()

        result_list = old_temp_tree.traverse_compare(file_id)

        for elem in result_list:
            self.storage_server.put(file_id + str(elem), self.cipher_text_list[name][elem])


        pre_list = []
        for elem in different_list:
            if elem[0]//32 == (elem[0]+len(elem[1]))//32:
                index_to_use = elem[0]//32
                partial_plain_text = value[index_to_use*32 : index_to_use*32+32] #This is the part of the text we need to redo encryption and also will make a change in mac
          
                IV = self.crypto.get_random_bytes(8)
                cipher_text = self.crypto.symmetric_encrypt(partial_plain_text, file_encryption_key, 'AES', 'CBC', IV+IV, None, None, None, 128)
            
                cipher_text = IV + cipher_text
                self.cipher_text_list[name][index_to_use] = cipher_text
                pre_list.append(index_to_use)
            else:
                storeing_index = ((elem[0]+len(elem[1]))- elem[0]//32*32)//32+1
                index_init = elem[0]//32
                for i in range(0, storeing_index):
                    index_to_use = index_init + i
                    partial_plain_text = value[index_to_use*32 : index_to_use*32+32]
                    IV = self.crypto.get_random_bytes(8)
                    cipher_text = self.crypto.symmetric_encrypt(partial_plain_text, file_encryption_key, 'AES', 'CBC', IV+IV, None, None, None, 128)
                    cipher_text = IV + cipher_text
                    self.cipher_text_list[name][index_to_use] = cipher_text

                    pre_list.append(index_to_use)




        hash_list = []
        for elem in self.cipher_text_list[name]:
            hash_list.append(self.crypto.cryptographic_hash(elem, 'SHA256'))
        new_temp_tree = MerkleTree(hash_list, self, name)

        new_temp_tree.pre_build()
        for elem in pre_list:
            new_temp_tree.modified(file_id, elem)
            self.storage_server.put(file_id + str(elem), self.cipher_text_list[name][elem])


        mac_text = self.crypto.message_authentication_code(new_temp_tree.root.val, file_mac_key, 'SHA256')
        self.storage_server.put(file_id +self.crypto.cryptographic_hash("mac", 'SHA256'), mac_text + str(len(self.cipher_text_list[name])))
      
       



    def download(self, name):
        """
        Download the users files provide name of the files. Given the key and the username has been entered
        """

        helper = self.string_concat(self.username, 'hello_world')
        uid = self.crypto.cryptographic_hash(helper, 'SHA256')
        helper2 = self.string_concat(self.username, 'dictionary')
        uid2 = self.crypto.cryptographic_hash(helper2, 'SHA256')
        helper3 = self.string_concat(self.username, 'sharing_dictionary')
        uid3 =self.crypto.cryptographic_hash(helper3,'SHA256')
        total_key = self.storage_server.get(uid)
        if total_key is None:
           return None
        else:
            #get the god key
            total_key = self.storage_server.get(uid)
            signed_God_key = total_key[:512]
            encrypted_God_key = total_key[512:]
            if not self.crypto.asymmetric_verify(encrypted_God_key, signed_God_key, self.pks.get_signature_key(self.username)):
                raise IntegrityError()
            God_key = self.crypto.asymmetric_decrypt(encrypted_God_key, self.elg_priv_key)
            if self.storage_server.get(uid2) is None:
                dictionary = {}
            else:
                total_dictionary = self.storage_server.get(uid2)
                encry_dictionary_mac = total_dictionary[:64]
                encry_dictionary = total_dictionary[64:]
                if self.crypto.message_authentication_code(encry_dictionary,self.crypto.cryptographic_hash(God_key + "Dictionary_mac",'SHA256'),'SHA256') !=encry_dictionary_mac :
                    raise IntegrityError()
                IV = encry_dictionary[:32]
                input_string = self.crypto.symmetric_decrypt(encry_dictionary[32:], self.crypto.cryptographic_hash(God_key,'SHA256'), 'AES','CBC',IV, None,None,None, 128)
                dictionary = json.loads(input_string)
                self.dictionary = dictionary
        total_shared_dictionary = self.storage_server.get(uid3)
        if total_shared_dictionary is None:
            self.shared_dictionary= {}
        else:
            encry_shared_dictionary = total_shared_dictionary[64:]
            encry_shared_dictionary_mac = total_shared_dictionary[:64]
            if self.crypto.message_authentication_code(encry_shared_dictionary,self.crypto.cryptographic_hash(God_key+ "shared_dictionary_mac",'SHA256'),'SHA256') != encry_shared_dictionary_mac :
                raise IntegrityError()
            IV = encry_shared_dictionary[:32]
            shared_dictionary_string = self.crypto.symmetric_decrypt(encry_shared_dictionary[32:],self.crypto.cryptographic_hash(God_key +"shared_dictionary" ,'SHA256'), 'AES','CBC',IV, None,None,None, 128)
            self.shared_dictionary = json.loads(shared_dictionary_string)

        if name in dictionary :
            current_key = dictionary[name]
            file_id = current_key[:8]
            file_key = current_key[8:]
        elif name in self.shared_dictionary:
        #download shared dictionary
            current_key = self.shared_dictionary[name]
            key_a_to_b = current_key [:16]
            id_a_to_b = current_key[16:]
            total_shared_key = self.storage_server.get(self.crypto.cryptographic_hash(id_a_to_b,'SHA256'))
            if total_shared_key is None:
                return None
            mac_shared_key = total_shared_key[:64]
            encrypt_shared_key = total_shared_key[64:]
            IV = encrypt_shared_key[:32]
            if self.crypto.message_authentication_code(encrypt_shared_key+ self.crypto.cryptographic_hash(id_a_to_b, 'SHA256'), self.crypto.cryptographic_hash(key_a_to_b+"key_ab_mac", 'SHA256'), 'SHA256') != mac_shared_key:
                raise IntegrityError()
            file_id_key = self.crypto.symmetric_decrypt(encrypt_shared_key[32:], self.crypto.cryptographic_hash(key_a_to_b,'SHA256'),'AES','CBC',IV, None,None,None, 128)
            file_id = file_id_key[:8]
            file_key = file_id_key[8:]
        else:
            return None

        mac_key = self.crypto.cryptographic_hash(file_id+ "hello_world", 'SHA256')
        encryption_key = self.crypto.cryptographic_hash(file_key,'SHA256')
        

        temp_name = self.crypto.cryptographic_hash(file_id + "temp_name" , 'SHA256')
        stored_root = self.storage_server.get(temp_name+ str(0) + "-" + str(0))
        if stored_root is None:
            return None
        if self.cipher_text_list is None or  name not in self.cipher_text_list:            
            return self.download_helper1(name, stored_root, file_id, encryption_key, mac_key)
        else:
            return self.download_helper2(name, stored_root, file_id, encryption_key, mac_key)



    def download_helper1(self, name, stored_root, file_id, encryption_key, mac_key):
        ret_mac = self.storage_server.get(file_id +self.crypto.cryptographic_hash("mac", 'SHA256'))

        if ret_mac is None:
            return None
        mac_text = ret_mac[:64]
        if self.crypto.message_authentication_code(stored_root, mac_key, 'SHA256') != mac_text:
            raise IntegrityError()
        downlength = int(ret_mac[64:])
        self.cipher_text_list[name] = []
        for i in range(0, downlength):
            self.cipher_text_list[name].append(self.storage_server.get(file_id + str(i)))

        hash_list = []
        for elem in self.cipher_text_list[name]:
            hash_list.append(self.crypto.cryptographic_hash(elem, 'SHA256'))
        new_temp_tree = MerkleTree(hash_list,self, name)
        new_temp_tree.pre_build()
        if new_temp_tree.root.val != stored_root:
            raise IntegrityError()
        plain_text_list = []
        for elem in self.cipher_text_list[name]:
            IV = elem[:16]
            plain_text_list.append(self.crypto.symmetric_decrypt(elem[16:], encryption_key, 'AES', 'CBC',IV+IV ,None, None,None, 128))
        self.stored_file[name] = ''.join(plain_text_list)
        return self.stored_file[name]



        




    def download_helper2(self, name, stored_root, file_id, encryption_key, mac_key):
       # Donwload helper 2. when we have not download file previously
        hash_list = []
        for elem in self.cipher_text_list[name]:
            hash_list.append(self.crypto.cryptographic_hash(elem, 'SHA256'))

        verify_tree = MerkleTree(hash_list, self, name)
        verify_tree.pre_build()

        result_list = verify_tree.traverse_download(file_id)
        
        if(result_list == []):
            return self.stored_file[name]
        for elem in result_list:
            
            self.cipher_text_list[name][elem] = self.storage_server.get(file_id + str(elem))
           
            IV = self.cipher_text_list[name][elem][:16]
           

        
        ret_mac = self.storage_server.get(file_id +self.crypto.cryptographic_hash("mac", 'SHA256'))
        if ret_mac is None:
            return None
        mac_text = ret_mac[:64]
        if self.crypto.message_authentication_code(stored_root, mac_key, 'SHA256') != mac_text:
            raise IntegrityError()
        downlength =int(ret_mac[64:])
        plain_text_list = []


        for elem in self.cipher_text_list[name]:
            IV = elem[:16]
            plain_text_list.append(self.crypto.symmetric_decrypt(elem[16:], encryption_key, 'AES', 'CBC',IV+IV ,None, None,None, 128))


        self.stored_file[name] = ''.join(plain_text_list)
        return self.stored_file[name]









    def share(self, user, name):
        """ Share the files under certain users with their username """
        receivers_elg_key = self.pks.get_encryption_key(user)
        file_folder = self.string_concat(self.username, name , 'sharing the file')

        helper = self.string_concat(self.username, 'hello_world')
        uid = self.crypto.cryptographic_hash(helper, 'SHA256')
        helper2 = self.string_concat(self.username, 'dictionary')
        uid2 = self.crypto.cryptographic_hash(helper2, 'SHA256')
        helper3 = self.string_concat(self.username, 'sharing_dictionary')
        uid3 =self.crypto.cryptographic_hash(helper3,'SHA256')

        total_key = self.storage_server.get(uid)
        if total_key is None:
            return None
        signed_God_key = total_key[:512]
        encrypted_God_key = total_key[512:]
        if not self.crypto.asymmetric_verify(encrypted_God_key, signed_God_key, self.pks.get_signature_key(self.username)):
            raise IntegrityError()
        God_key = self.crypto.asymmetric_decrypt(encrypted_God_key, self.elg_priv_key)
        total_dictionary = self.storage_server.get(uid2)
        total_shared_dictionary = self.storage_server.get(uid3)

        ret_msg = None
        key_a_to_b = None
        if not total_dictionary is None:
            encry_dictionary_mac = total_dictionary[:64]
            encry_dictionary = total_dictionary[64:]
            IV = encry_dictionary[:32]
            if self.crypto.message_authentication_code(encry_dictionary,self.crypto.cryptographic_hash(God_key+ "Dictionary_mac",'SHA256'),'SHA256') !=encry_dictionary_mac :
                raise IntegrityError()
            input_string = self.crypto.symmetric_decrypt(encry_dictionary[32:],self.crypto.cryptographic_hash(God_key,'SHA256'), 'AES','CBC',IV, None,None,None, 128)
            dictionary = json.loads(input_string)
            if name in dictionary:
                current_key = dictionary[name]
                file_id = current_key[:8]
                file_key = current_key[8:]
                #it is ur own files send to others
                key_a_to_b = self.crypto.get_random_bytes(8)
                id_a_to_b=self.string_concat(self.username , "share with" , user , "with file", self.crypto.cryptographic_hash(key_a_to_b, 'SHA256'))
                IV = self.crypto.get_random_bytes(16)
                encrypt_shared_key = IV+ self.crypto.symmetric_encrypt(file_id + file_key , self.crypto.cryptographic_hash(key_a_to_b, 'SHA256'),'AES','CBC',IV, None,None,None, 128)
                mac_shared_key = self.crypto.message_authentication_code(encrypt_shared_key+self.crypto.cryptographic_hash(id_a_to_b,'SHA256'), self.crypto.cryptographic_hash(key_a_to_b + "key_ab_mac", 'SHA256'), 'SHA256')
                self.storage_server.put(self.crypto.cryptographic_hash(id_a_to_b,'SHA256'), mac_shared_key+ encrypt_shared_key)
                encry_msg =self.crypto.asymmetric_encrypt(key_a_to_b + id_a_to_b , self.pks.get_encryption_key(user))
                signed_msg = self.crypto.asymmetric_sign(encry_msg, self.rsa_priv_key)
                ret_msg = signed_msg+encry_msg
        if not total_shared_dictionary is None:
            encry_shared_dictionary = total_shared_dictionary[64:]
            encry_shared_dictionary_mac = total_shared_dictionary[:64]
            IV = encry_shared_dictionary[:32]
            if self.crypto.message_authentication_code(encry_shared_dictionary,self.crypto.cryptographic_hash(God_key + "shared_dictionary_mac",'SHA256'),'SHA256') != encry_shared_dictionary_mac :
                raise IntegrityError()
            shared_dictionary_string = self.crypto.symmetric_decrypt(encry_shared_dictionary[32:],self.crypto.cryptographic_hash(God_key + "shared_dictionary",'SHA256'), 'AES','CBC',IV, None,None,None, 128)
            self.shared_dictionary = json.loads(shared_dictionary_string)
            if name in self.shared_dictionary:
                #meanin we are not the ownders.
                current_key = self.shared_dictionary[name]
                encry_msg =self.crypto.asymmetric_encrypt(current_key , self.pks.get_encryption_key(user))
                signed_msg = self.crypto.asymmetric_sign(encry_msg, self.rsa_priv_key)
                ret_msg = signed_msg+encry_msg

        #let us get the tree helpful for this folder
        sharing_tree = self.storage_server.get(self.crypto.cryptographic_hash(file_folder, 'SHA256'))
        if sharing_tree is None:
            #we maybe have not share with anyone yet so firstly, create a enmpty dictionary
            sharing_dict ={}
        else:
            #we have shared with someone retrivet sharing dict ffrom the tree
            mac_sharing_dict = sharing_tree[:64]
            encry_sharing_dict = sharing_tree[64:]
            IV = encry_sharing_dict[:32]
            if self.crypto.message_authentication_code(encry_sharing_dict, self.crypto.cryptographic_hash(God_key + "The_sharing_tree_mac",'SHA256'),'SHA256') != mac_sharing_dict:
                raise IntegrityError()
            sharing_dict_string = self.crypto.symmetric_decrypt(encry_sharing_dict[32:], self.crypto.cryptographic_hash(God_key + "The_sharing_tree", 'SHA256'), 'AES','CBC',IV, None,None,None, 128)
            sharing_dict = json.loads(sharing_dict_string)
        if user in sharing_dict:
            return None #if we already share with Bob?
        else:
            if key_a_to_b is not None:
                sharing_dict[user] =key_a_to_b+id_a_to_b
        sharing_dict_string = json.dumps(sharing_dict)
        IV = self.crypto.get_random_bytes(16)
        new_encry_sharing_dict = IV + self.crypto.symmetric_encrypt(sharing_dict_string, self.crypto.cryptographic_hash(God_key + "The_sharing_tree", 'SHA256'), 'AES','CBC',IV, None,None,None, 128)
        new_mac_sharing_dict = self.crypto.message_authentication_code(new_encry_sharing_dict, self.crypto.cryptographic_hash(God_key+ "The_sharing_tree_mac",'SHA256'),'SHA256')
        self.storage_server.put(self.crypto.cryptographic_hash(file_folder, 'SHA256'), new_mac_sharing_dict + new_encry_sharing_dict)
        return ret_msg






    def receive_share(self, from_username, newname, message):
        """ From recepient side, inform the share has been complete and download to the local disk """
        if message is None:
            return None

        signed_msg = message[:512]
        encry_msg = message[512:]
        if not self.crypto.asymmetric_verify(encry_msg, signed_msg, self.pks.get_signature_key(from_username)):
            return None
            raise IntegrityError()
        total_current_key = self.crypto.asymmetric_decrypt(encry_msg, self.elg_priv_key)

        key_a_to_b = total_current_key[:16]
        id_a_to_b = total_current_key[16:]
        helper = self.string_concat(self.username, 'hello_world')
        uid = self.crypto.cryptographic_hash(helper, 'SHA256')
        helper3 = self.string_concat(self.username, 'sharing_dictionary')
        uid3 =self.crypto.cryptographic_hash(helper3,'SHA256')




        total_key = self.storage_server.get(uid)
        if self.storage_server.get(uid) is None:
            dictionary = {}
            input_string = json.dumps(dictionary)
            God_key = self.crypto.get_random_bytes(16)
            encrypted_God_key= self.crypto.asymmetric_encrypt(God_key, self.pks.get_encryption_key(self.username))

            signed_God_key = self.crypto.asymmetric_sign(encrypted_God_key, self.rsa_priv_key)
            self.storage_server.put(uid, signed_God_key+encrypted_God_key)
            #let encrypt the dictionary now
            IV = self.crypto.get_random_bytes(16)
            encry_dictionary = IV + self.crypto.symmetric_encrypt(input_string, self.crypto.cryptographic_hash(God_key + "shared_dictionary",'SHA256'), 'AES','CBC',IV, None,None,None, 128)
            encry_dictionary_mac = self.crypto.message_authentication_code(encry_dictionary, self.crypto.cryptographic_hash(God_key + "shared_dictionary_mac",'SHA256'), 'SHA256')
            self.storage_server.put(uid3, encry_dictionary_mac+encry_dictionary)
        else:
            #should we do anything??
            #at least get the god key
            total_key = self.storage_server.get(uid)
            signed_God_key = total_key[:512]
            encrypted_God_key = total_key[512:]
            if not self.crypto.asymmetric_verify(encrypted_God_key, signed_God_key, self.pks.get_signature_key(self.username)):
                raise IntegrityError()
            God_key = self.crypto.asymmetric_decrypt(encrypted_God_key, self.elg_priv_key)
            #we have the god key now

            if self.storage_server.get(uid3) is None:
                shared_dictionary = {}
                self.shared_dictionary = shared_dictionary
                input_string = json.dumps(shared_dictionary)
                IV = self.crypto.get_random_bytes(16)
                encry_dictionary = IV + self.crypto.symmetric_encrypt(input_string, self.crypto.cryptographic_hash(God_key+ "shared_dictionary",'SHA256'), 'AES','CBC',IV, None,None,None, 128)
                encry_dictionary_mac = self.crypto.message_authentication_code(encry_dictionary, self.crypto.cryptographic_hash(God_key + "shared_dictionary_mac",'SHA256'), 'SHA256')
                self.storage_server.put(uid3, encry_dictionary_mac+encry_dictionary)
            else:
                total_dictionary = self.storage_server.get(uid3)
                encry_dictionary_mac = total_dictionary[:64]
                encry_dictionary = total_dictionary[64:]
                IV = encry_dictionary[:32]
                if self.crypto.message_authentication_code(encry_dictionary,self.crypto.cryptographic_hash(God_key + "shared_dictionary_mac",'SHA256'),'SHA256') !=encry_dictionary_mac :
                    raise IntegrityError()
                input_string = self.crypto.symmetric_decrypt(encry_dictionary[32:],self.crypto.cryptographic_hash(God_key + "shared_dictionary",'SHA256'), 'AES','CBC',IV, None,None,None, 128)
                self.shared_dictionary = json.loads(input_string)
              

        self.shared_dictionary[newname] = key_a_to_b + id_a_to_b
        new_dict_string = json.dumps(self.shared_dictionary)
        IV = self.crypto.get_random_bytes(16)
        new_dict_cipher = IV+ self.crypto.symmetric_encrypt(new_dict_string, self.crypto.cryptographic_hash(God_key + "shared_dictionary",'SHA256'), 'AES','CBC',IV, None,None,None, 128)
        new_dict_mac = self.crypto.message_authentication_code(new_dict_cipher, self.crypto.cryptographic_hash(God_key + "shared_dictionary_mac",'SHA256'), 'SHA256')
        self.storage_server.put(uid3, new_dict_mac+new_dict_cipher)

        self.download(newname)
    

 



    def revoke(self, user, name):
        """revoke sharing with user by username"""

        helper = self.string_concat(self.username, 'hello_world')
        uid = self.crypto.cryptographic_hash(helper, 'SHA256')
        helper2 = self.string_concat(self.username, 'dictionary')
        uid2 = self.crypto.cryptographic_hash(helper2, 'SHA256')

        value = self.download(name)
        total_key = self.storage_server.get(uid)
        if total_key is None:
            return None
        else:
            total_key = self.storage_server.get(uid)
            signed_God_key = total_key[:512]
            encrypted_God_key = total_key[512:]
            if not self.crypto.asymmetric_verify(encrypted_God_key, signed_God_key, self.pks.get_signature_key(self.username)):
                raise IntegrityError()
            God_key = self.crypto.asymmetric_decrypt(encrypted_God_key, self.elg_priv_key)
            if self.storage_server.get(uid2) is None:
                return None
            else:
                total_dictionary = self.storage_server.get(uid2)
                encry_dictionary_mac = total_dictionary[:64]
                encry_dictionary = total_dictionary[64:]
                IV = encry_dictionary[:32]
                if self.crypto.message_authentication_code(encry_dictionary,self.crypto.cryptographic_hash(God_key + "Dictionary_mac",'SHA256'),'SHA256') !=encry_dictionary_mac :
                    raise IntegrityError()
                input_string = self.crypto.symmetric_decrypt(encry_dictionary[32:],self.crypto.cryptographic_hash(God_key,'SHA256'), 'AES','CBC',IV, None,None,None, 128)
                dictionary = json.loads(input_string)
                self.dictionary = dictionary
        if name in dictionary :
            file_id = self.crypto.get_random_bytes(4)
            file_key = self.crypto.get_random_bytes(4)
            dictionary[name] = file_id + file_key
        else:
            return None
        mac_key = self.crypto.cryptographic_hash(file_id+ "hello_world" , 'SHA256')

        encryption_key = self.crypto.cryptographic_hash(file_key,'SHA256')
        self.upload_helper1(name, file_id, mac_key, encryption_key, value)
        new_dict_string = json.dumps(dictionary)
        IV = self.crypto.get_random_bytes(16)
        new_dict_cipher = IV + self.crypto.symmetric_encrypt(new_dict_string, self.crypto.cryptographic_hash(God_key,'SHA256'), 'AES','CBC',IV, None,None,None, 128)
        new_dict_mac = self.crypto.message_authentication_code(new_dict_cipher, self.crypto.cryptographic_hash(God_key + "Dictionary_mac",'SHA256'), 'SHA256')
        self.storage_server.put(uid2, new_dict_mac+new_dict_cipher)
        

        file_folder = self.string_concat(self.username, name , 'sharing the file')
        sharing_tree = self.storage_server.get(self.crypto.cryptographic_hash(file_folder, 'SHA256'))
        if sharing_tree is None:
            return None
        else:
            mac_sharing_dict = sharing_tree[:64]
            encry_sharing_dict = sharing_tree[64:]
            IV = encry_sharing_dict[:32]
            if self.crypto.message_authentication_code(encry_sharing_dict, self.crypto.cryptographic_hash(God_key + "The_sharing_tree_mac",'SHA256'),'SHA256') != mac_sharing_dict:
                raise IntegrityError()
            sharing_dict_string = self.crypto.symmetric_decrypt(encry_sharing_dict[32:],  self.crypto.cryptographic_hash(God_key + "The_sharing_tree", 'SHA256'), 'AES','CBC',IV, None,None,None, 128)
            sharing_dict = json.loads(sharing_dict_string)

        if user in sharing_dict:
            id_a_to_b = sharing_dict[user][16:]
            key_a_to_b = sharing_dict[user][:16]
            del sharing_dict[user]
        else:
            return None


        id_a_to_b=self.string_concat(self.username , "share with" , user , "with file", self.crypto.cryptographic_hash(key_a_to_b, 'SHA256'))
        self.storage_server.delete(self.crypto.cryptographic_hash(id_a_to_b,'SHA256'))


        for user_elem in sharing_dict:
            priv_key = sharing_dict[user_elem]
            key_a_to_b = priv_key[:16]
            id_a_to_b = priv_key[16:]
            IV = self.crypto.get_random_bytes(16)
            encrypt_shared_key = IV + self.crypto.symmetric_encrypt(file_id + file_key , self.crypto.cryptographic_hash(key_a_to_b, 'SHA256'),'AES','CBC',IV, None,None,None, 128)
            mac_shared_key = self.crypto.message_authentication_code(encrypt_shared_key+ self.crypto.cryptographic_hash(id_a_to_b,'SHA256'), self.crypto.cryptographic_hash(key_a_to_b + "key_ab_mac", 'SHA256'), 'SHA256')
            self.storage_server.put(self.crypto.cryptographic_hash(id_a_to_b,'SHA256'), mac_shared_key+ encrypt_shared_key)


        sharing_dict_string = json.dumps(sharing_dict)
        IV = self.crypto.get_random_bytes(16)
        new_encry_sharing_dict = IV+ self.crypto.symmetric_encrypt(sharing_dict_string, self.crypto.cryptographic_hash(God_key + "The_sharing_tree", 'SHA256'), 'AES','CBC',IV, None,None,None, 128)
        new_mac_sharing_dict = self.crypto.message_authentication_code(new_encry_sharing_dict, self.crypto.cryptographic_hash(God_key + "The_sharing_tree_mac",'SHA256'),'SHA256')
        self.storage_server.put(self.crypto.cryptographic_hash(file_folder, 'SHA256'), new_mac_sharing_dict + new_encry_sharing_dict)


















