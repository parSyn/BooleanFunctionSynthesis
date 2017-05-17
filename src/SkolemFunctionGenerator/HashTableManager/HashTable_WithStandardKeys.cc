/***************************************************************************
FileName : HashTable_WithStandardKeys.cc

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Description: This file contains an implementation of hash tables

Copyright (C) 2017  Supratik Chakraborty

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
************************************************************/

#include "HashTable_WithStandardKeys.h"
#include<list>
class t_Signal;
using namespace std;

//
//template <class t_Value>
//inline bool t_HTStatusValue<t_Value> ::success()
//{
//
//  return m_isSuccess;
//}
//
//template <class t_Value>
//inline t_Value t_HTStatusValue<t_Value> ::getValue()
//{
//  return m_value;
//}
//
//template <class t_Value>
//t_HTStatusValue<t_Value> ::t_HTStatusValue(bool status_to_update, t_Value v)
//{
//  m_value = v;
//  m_isSuccess = status_to_update;
//}

template <class t_Key, class t_Value>
inline t_Key t_HashTable <t_Key,t_Value>:: t_HashTableEntry :: getKey()
{
  return m_key;
}

template <class t_Key, class t_Value>
inline t_Value t_HashTable <t_Key,t_Value>:: t_HashTableEntry :: getValue()
{
  return m_value;
}

template <class t_Key, class t_Value>
t_HashTable <t_Key,t_Value>:: t_HashTableEntry :: t_HashTableEntry():first(m_key), second(m_value)
{
}

template <class t_Key, class t_Value>
t_HashTable <t_Key,t_Value>:: t_HashTableEntry :: t_HashTableEntry (const t_Value& value_of_entry, const t_Key& key_of_entry):
first(m_key), second(m_value)
{
  m_value = value_of_entry;
  m_key = key_of_entry;
  m_next = NULL;
}

template <class t_Key, class t_Value>
inline void t_HashTable <t_Key,t_Value>:: t_HashTableEntry:: printHashTableEntry()
{
  cout<<"Key: "<<m_key<<" ";
  //          cout<<"Value :"<<value<<endl;
}





template <class t_Key, class t_Value>
t_HashTable <t_Key,t_Value>:: t_HashTableEntryListHeader :: t_HashTableEntryListHeader()
{
  m_next = NULL;
}




template <class t_Key, class t_Value>
inline t_index  t_HashTable<t_Key, t_Value> ::Hash(const string& string_to_hash)
{
  /* needs three primes; 
     assumes hashtable's size (m_Buckets.size()) is a prime;
     PRIME0, PRIME1 are both assumed to be < hashtable's size */

  int hashval = 0;
  int i=0;
  while (string_to_hash[i]) {
    char c = string_to_hash[i];
    hashval = (hashval*PRIME0 + c*PRIME1) % m_Buckets.size();
    i++;
  }
  return hashval;
}
#ifdef KEEP_INT_HASH
template <class t_Key, class t_Value>
inline t_index  t_HashTable<t_Key, t_Value> ::Hash(int integer_to_hash)
{
  /* needs just two primes; 
     hashtable's size (m_Buckets.size()) is assumed to be a prime 
     PRIME1 is assumed to be less than hashtable's size
  */
  int hashval = 0;
  while (integer_to_hash != 0) {
    int lastbit = integer_to_hash & 1;
    integer_to_hash = integer_to_hash >> 1;
    hashval = (hashval + lastbit*PRIME1) % m_Buckets.size();
  }
  return hashval;
}
#endif
template <class t_Key, class t_Value>
inline t_index  t_HashTable<t_Key, t_Value> ::Hash(unsigned long long int integer_to_hash)
{
  /* needs just two primes; 
     hashtable's size (m_Buckets.size()) is assumed to be a prime 
     PRIME1 is assumed to be less than hashtable's size
  */
  int hashval = 0;
  while (integer_to_hash != 0) {
    int lastbit = integer_to_hash & 1;
    integer_to_hash = integer_to_hash >> 1;
    hashval = (hashval*PRIME0 + lastbit*PRIME1) % m_Buckets.size();
  }
  return hashval;
}

template<class t_Key, class t_Value>
vector<unsigned> t_HashTable<t_Key, t_Value>::getCollisionCounts()const
{
    vector<unsigned> coll;
    for(int i=0; i<m_Buckets.size(); i++)
    {
        t_HashTableEntryListHeader head = m_Buckets[i];
        t_HashTableEntry *entry = head.m_next;
        unsigned count=0;
        while(entry != NULL)
        {
            entry = entry->m_next;
            ++count;
        }
        coll.push_back(count);
    }
    return coll;
}

template <class t_Key, class t_Value>
inline bool  t_HashTable<t_Key, t_Value> ::CompareKeys(const string& key1, const string& key2)
{
  if(! key1.compare(key2))
    return true;
  return false;
}
template <class t_Key, class t_Value>
inline bool  t_HashTable<t_Key, t_Value> ::CompareKeys(const int key1, const int key2)
{
  return (key1 == key2);
}

template <class t_Key, class t_Value>
inline bool  t_HashTable<t_Key, t_Value> ::insertEntryInList(const t_index& index,const t_Value& value_to_insert, const t_Key& key)
{
  t_HashTableEntryListHeader head=m_Buckets[index];

  if(head.m_next == NULL)
    {

      t_HashTableEntry *entry_to_insert = new t_HashTableEntry (value_to_insert, key);
      if (entry_to_insert == NULL) {
	cerr << "Memory allocation failure while adding entry to HashTable" << endl;
	return false;
      }

      entry_to_insert->m_next = NULL;
      (m_Buckets[index]).m_next = entry_to_insert;
      m_nBucketsUsed +=1; //head.m_next=1 means this is new bucket
      return true;
    }
  else if(head.m_next != NULL)
    {
      t_HashTableEntryListHeader head = m_Buckets[index]; //head cannot be null here
      t_HashTableEntry *entry = head.m_next;
      while(entry->m_next != NULL)
	{
	  entry = entry->m_next;
	}
      t_HashTableEntry *entry_to_insert = new t_HashTableEntry (value_to_insert, key);
      if (entry_to_insert == NULL) {
	cerr << "Memory allocation failure while adding entry to HashTable" << endl;
	return false;
      }

      entry_to_insert->m_next = NULL;
      entry->m_next = entry_to_insert;
      m_nCollisions += 1;

      return true;
    }
  return true;
}


template <class t_Key, class t_Value>
inline bool  t_HashTable<t_Key, t_Value> :: freeDynamicallyAllocatedMemory()
{
  int counter = 0;
  int size = m_Buckets.size();
  for(int i=0;i<size;i++)
    {
      t_HashTableEntryListHeader &head = m_Buckets[i];
      if(head.m_next == NULL)
	{
	  continue;
	}
      else
	{
	  t_HashTableEntry *current_entry = head.m_next;
	  while(current_entry!= NULL)
	    {
	      t_HashTableEntry *entry_to_delete = current_entry;
	      current_entry = current_entry->m_next;
	      delete(entry_to_delete);
	      counter ++;
	    }
	  head.m_next = NULL;
	}
    }
  //cout<<"Freeed "<<counter << " number of entrys \n";
  return true;
}


  
template <class t_Key, class t_Value>
t_HashTable<t_Key, t_Value> ::t_HashTable()
{
  m_nKeysStored = 0;
  m_nCollisions = 0;
  m_nBucketsUsed = 0;
#ifdef DEBUG
  cout<<"Created the HashTable \n";
#endif
  t_HashTableEntryListHeader entryHeader;
  m_Buckets.resize(m_SIZE, entryHeader);
#ifdef DEBUG
  cout<<"HashTable size is "<<m_Buckets.size()<<endl;
#endif
}

template <class t_Key, class t_Value>
t_HashTable<t_Key, t_Value> ::t_HashTable(int size)
{
  m_nKeysStored = 0;
  m_nCollisions = 0;
  m_nBucketsUsed = 0;
  cout<<"Created the HashTable \n";
  t_HashTableEntryListHeader entryHeader;
  if(size<=0)
    {
      cerr<<"Invalid value for size entered  "<<size<<endl;
      cerr<<"Abnormal termination\n";
      cerr<<"Exiting\n";
      exit(0);
    }

  m_Buckets.resize(size, entryHeader);
  cout<<"HashTable size is "<<m_Buckets.size()<<endl;
}
template <class t_Key, class t_Value>
t_HashTable<t_Key, t_Value> ::~t_HashTable()
{
  //Release the resources allocated to the HashTable entrys
  //cout<<"Freeing the memory\n";
  bool free_mem_result = freeDynamicallyAllocatedMemory();
}

template <class t_Key, class t_Value>
inline bool  t_HashTable<t_Key, t_Value> ::clear()
{
  bool free_mem_result = freeDynamicallyAllocatedMemory();
  if(!free_mem_result)
    {
      return false;
    }
  else
    {
      m_nKeysStored = 0;
      m_nCollisions = 0;
      m_nBucketsUsed = 0;
      return true;
    }
}

template <class t_Key, class t_Value>
inline t_HTStatusValue<t_Value>  t_HashTable<t_Key, t_Value> ::hashtable_insert(const t_Key& key, const t_Value& val)
{
  t_HTStatusValue <t_Value> s = hashtable_search(key);
  if(s.success())
    {
      // a entry with this key exists in the hashtable
      t_HTStatusValue <t_Value> result (false, s.getValue());
      return result;
    }

  t_index index = Hash(key); //the hash functions always return 0<= Hash(key) <m_SIZE

  bool insert_result = insertEntryInList(index, val, key);
  if(insert_result==false)
    {
      t_Value Dummy_Val=t_Value();
	  
      t_HTStatusValue <t_Value> result (false, Dummy_Val);
      return result;
    }
  t_HTStatusValue <t_Value> result (true, val);
  m_nKeysStored+=1;
  return result;
}


/**
 *The deletion of a value takes a reference to value. However, we cannot delete it directly. Need to search...
 *
 **/
template <class t_Key, class t_Value>
inline t_HTStatusValue<t_Value>  t_HashTable<t_Key, t_Value> ::hashtable_delete(const t_Key& key)
{
  //REVIEW THIS CODE THOUROUGHLY
  t_index index = Hash(key);
  t_HashTableEntryListHeader head = m_Buckets[index];

  if(head.m_next == NULL)
    {
      t_Value DummyValue=t_Value();

      t_HTStatusValue <t_Value> result(false, DummyValue);
      return result;
    }

  else
    {
      t_HashTableEntry *entry = head.m_next; //head cannot be null here
      t_HashTableEntry *prev = NULL; //must specify the starting condition
      while(entry!=NULL)
	{
	  t_Key current_key = entry->getKey();
	  if(CompareKeys(current_key,key))
	    {
	      t_HTStatusValue <t_Value> result(true, entry->getValue());
	      t_HashTableEntry *entry_to_delete = entry;
	      m_nKeysStored-=1;
	      if(prev == NULL)
		{
		  //first entry in the list
		  (m_Buckets[index]).m_next = entry->m_next;
		  // entry = entry->m_next;
		  delete(entry_to_delete);
		  m_nBucketsUsed -=1; //We are releasing this bucket...
		  return result;
		}
	      else if(entry->m_next==NULL)
		{
		  //last but not the first entry in the list
		  prev->m_next = entry->m_next;
		  delete(entry_to_delete);
		  m_nCollisions -= 1;
		  return result;
		}
	      else
		{
		  //middle entry in the list
		  prev->m_next = entry->m_next;
		  // entry = entry->m_next;
		  delete(entry_to_delete);
		  m_nCollisions -= 1;
		  return result;
		}
	    }
	  else
	    {
	      prev = entry;
	      entry = entry->m_next;
	    }
	}
    }

  t_Value DummyValue=t_Value();
  t_HTStatusValue <t_Value> result(false, DummyValue);

  return result;
}


template <class t_Key, class t_Value>
inline t_HTStatusValue<t_Value>  t_HashTable<t_Key, t_Value> ::hashtable_search(const t_Key& key)
{

  t_index index = Hash(key);

  t_HashTableEntryListHeader head = m_Buckets[index];
  if(head.m_next == NULL)
    {

      t_Value Dummy_Val= t_Value();
      t_HTStatusValue <t_Value> result (false, Dummy_Val);
      return result;
    }
  else
    {
      t_HashTableEntryListHeader head = m_Buckets[index]; //head cannot be null here
      t_HashTableEntry *entry = head.m_next;
      while(entry != NULL)
	{
	  t_Key current_key = (t_Key)(entry->getKey());
	  if(CompareKeys(current_key,key))
	    {
	      t_HTStatusValue <t_Value> result (true, entry->getValue());
	      return result;
	    }
	  entry = entry->m_next;
	}

      t_Value Dummy_Val=t_Value();
      t_HTStatusValue <t_Value> result (false, Dummy_Val);
      return result;

    }
}

template <class t_Key, class t_Value>
inline t_Value&  t_HashTable<t_Key, t_Value> ::operator[](const t_Key& key)
{

  t_index index = Hash(key);

  t_HashTableEntryListHeader head = m_Buckets[index];
  if(head.m_next == NULL)
    {

      t_Value Dummy_Val;
      //t_HTStatusValue <t_Value> result (false, Dummy_Val);
      hashtable_insert(key, Dummy_Val);
      return (*this)[key];
      //return result;
    }
  else
    {
      t_HashTableEntryListHeader head = m_Buckets[index]; //head cannot be null here
      t_HashTableEntry *entry = head.m_next;
      while(entry != NULL)
	{
	  t_Key current_key = (t_Key)(entry->getKey());
	  if(CompareKeys(current_key,key))
	    {
	      //t_HTStatusValue <t_Value> result (true, entry->getValue());
	      //return result;
              return entry->m_value;
	    }
	  entry = entry->m_next;
	}

      t_Value Dummy_Val;
      hashtable_insert(key, Dummy_Val);
      return (*this)[key];
      //t_HTStatusValue <t_Value> result (false, Dummy_Val);
      //return result;

    }
}

template <class t_Key, class t_Value>
inline HashTableIterator<t_Key, t_Value>  t_HashTable<t_Key, t_Value>::find(const t_Key& key)
{

  t_index index = Hash(key);

  t_HashTableEntryListHeader head = m_Buckets[index];
  if(head.m_next == NULL)
    {

      //t_Value Dummy_Val;
      //t_HTStatusValue <t_Value> result (false, Dummy_Val);
      return end();
      //return result;
    }
  else
    {
      t_HashTableEntryListHeader head = m_Buckets[index]; //head cannot be null here
      t_HashTableEntry *entry = head.m_next;
      while(entry != NULL)
	{
	  t_Key current_key = (t_Key)(entry->getKey());
	  if(CompareKeys(current_key,key))
	    {
	      //t_HTStatusValue <t_Value> result (true, entry->getValue());
	      //return result;
              return HashTableIterator<t_Key,t_Value>(*this, index, entry);
	    }
	  entry = entry->m_next;
	}

      return end();
      //t_HTStatusValue <t_Value> result (false, Dummy_Val);
      //return result;

    }
}
/**
 * This function prints the hashtable, but only when standard values are used. Not otherwise.
 *
 *
 */
template <class t_Key, class t_Value>
inline void t_HashTable<t_Key, t_Value> :: printHashTableKeys()
{

  cout<<"Printing the keys in the hashtable\n";
  //if somebody wants values as well, then he can use
  //1. hashtable_search(key)
  //2. print the value associated with key
  t_index index = 0;

  for(index =0;index<m_SIZE;index++)
    {
      t_HashTableEntryListHeader head = m_Buckets[index];
      t_HashTableEntry *entry = head.m_next;

      //cout<<"HashTable index:"<<index<<" : ";
      while(entry != NULL)
	{
	  entry->printHashTableEntry();
	  entry = entry->m_next;
	}
      //      cout<<endl;
    }

}

/* Statistics collecting functions */
template <class t_Key, class t_Value>
inline int t_HashTable<t_Key, t_Value> :: getMaximumSizeOfHashTable()
{
  return m_SIZE;
}

template <class t_Key, class t_Value>
inline float  t_HashTable<t_Key, t_Value> ::getLoadFactor()
{
  return ((float)m_nKeysStored/m_SIZE); //Load factor w.r.t. size

}

template <class t_Key, class t_Value>
inline int t_HashTable <t_Key,t_Value>:: getStoredKeysCount()
{
  return m_nKeysStored;
}

template <class t_Key, class t_Value>
inline int t_HashTable <t_Key,t_Value>:: getCountOfCollisions()
{
  return m_nCollisions;
}
template <class t_Key, class t_Value>
inline int t_HashTable<t_Key, t_Value> :: getNumberOfBucketsUsed()
{
  return m_nBucketsUsed;
}



template class t_HashTable<int,int>;
template class t_HTStatusValue<int>;

/**
  Putting classes as arbitrary types does not work
  This means following code will not work
  template class t_HashTable<string,MyValue> ;
  template class t_HTStatusValue<MyValue>;
*/

template class t_HashTable<string,int>;
template class t_HashTable<string, list<string>* >;
template class t_HashTable<string, bool>;
template class t_HashTable<unsigned long long int, bool>;
template class t_HashTable<string,vector<pair<int,int> > >;
template class t_HashTable<unsigned long int, set<string> >;
template class t_HashTable<unsigned long int, int >;
template class t_HashTable<unsigned long int, string >;
template class t_HashTable<string, set<string> >;
template class t_HashTable<int, set<string> >;
template class t_HashTable<int, bool>;

struct Aig_Obj_t;
template class t_HashTable<int, Aig_Obj_t* >;
template class t_HTStatusValue<Aig_Obj_t*>;
