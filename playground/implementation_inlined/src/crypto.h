#ifndef CRYPTO_H
#define CRYPTO_H

    //Protocol definitions, how many data blocks and sequence number blocks we have
    //Each block is 1 byte and the MSB is header information
    #define NUM_DATA_BLOCKS         8
    #define NUM_SEQNO_BLOCKS        2
    #define MSG_SIZE                (NUM_DATA_BLOCKS+NUM_SEQNO_BLOCKS)

    //Definitions for the crypto key, the number of blocks as well as the block size
    #define NUM_KEY_BLOCKS          10
    #define KEY_BLOCK_SIZE          NUM_DATA_BLOCKS
    #define KEY_SIZE                (NUM_KEY_BLOCKS * KEY_BLOCK_SIZE)

    void process_messages(char *key);

#endif /*CRYPTO_H*/
