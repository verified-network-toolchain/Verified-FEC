//The parts of netinet/ip.h that we need, modified to remove bitfields

#include <sys/types.h>

#include <netinet/in.h>


/*
 * Definitions for internet protocol version 4.
 * Per RFC 791, September 1981.
 */

/*
 * Structure of an internet header, naked of options.
 */
struct ip
  {
    unsigned char ip_hl_v; // JOSH - removed bitfields
//#if __BYTE_ORDER == __LITTLE_ENDIAN
//    unsigned int ip_hl:4;     /* header length */
//    unsigned int ip_v:4;      /* version */
//#endif
//#if __BYTE_ORDER == __BIG_ENDIAN
//    unsigned int ip_v:4;      /* version */
//    unsigned int ip_hl:4;     /* header length */
//#endif
    uint8_t ip_tos;         /* type of service */
    unsigned short ip_len;      /* total length */
    unsigned short ip_id;       /* identification */
    unsigned short ip_off;      /* fragment offset field */
#define IP_RF 0x8000            /* reserved fragment flag */
#define IP_DF 0x4000            /* dont fragment flag */
#define IP_MF 0x2000            /* more fragments flag */
#define IP_OFFMASK 0x1fff       /* mask for fragmenting bits */
    uint8_t ip_ttl;         /* time to live */
    uint8_t ip_p;           /* protocol */
    unsigned short ip_sum;      /* checksum */
    struct in_addr ip_src, ip_dst;  /* source and dest address */
  };