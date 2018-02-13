

#include "uart.h"
#include "crypto.h"

void main ( ) {
    uart_init();
    //Send Welcome
    uart_send_string ("\nBBC micro:bit echo\n");
    // process messages and encrypt
    process_messages();
}
