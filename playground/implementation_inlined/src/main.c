

#include "uart.h"
#include "crypto.h"

void test_fill_key(char *key){
  for(int i = 0; i < 8 * 16383; i++){
    key[i] = i*i*i % 256;
  }
}

void main ( ) {
    uart_init();
    //Send Welcome
    uart_send_string ("\nBBC micro:bit echo\n");

    char key[8*16383];
    test_fill_key(key);

    // process messages and encrypt
    process_messages(key);
}
