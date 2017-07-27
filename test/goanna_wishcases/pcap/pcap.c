/* from libpcap-1.0.0/pcap-linux.c */

#include <assert.h>

#define TPACKET_ALIGNMENT        16
#define TPACKET_ALIGN(x) (((x)+TPACKET_ALIGNMENT-1)&~(TPACKET_ALIGNMENT-1))
struct tpacket_req {
        unsigned int    tp_block_size;  /* Minimal size of contiguous block */
        unsigned int    tp_block_nr;    /* Number of blocks */
        unsigned int    tp_frame_size;  /* Size of frame */
        unsigned int    tp_frame_nr;    /* Total number of frames */
};
struct sockaddr_ll {
        unsigned short  sll_family;
        unsigned short  sll_protocol;
        int             sll_ifindex;
        unsigned short  sll_hatype;
        unsigned char   sll_pkttype;
        unsigned char   sll_halen;
        unsigned char   sll_addr[8];
};

struct pcap_md {
	unsigned int	tp_hdrlen;
};
struct pcap_opt {
        int     buffer_size;
        char    *source;
        int     promisc;
        int     rfmon;
};
struct pcap {
	unsigned int	snapshot;
	struct pcap_md	md;
	struct pcap_opt	opt;
};
typedef struct pcap	pcap_t;

static unsigned int
getpagesize(void)
{
	return 4096;
}

static void
compute_ring_block(int frame_size, unsigned int *block_size, unsigned int *frames_per_block)
{
        *block_size = getpagesize();
        while (*block_size < frame_size)
                *block_size <<= 1;
								/* Goanna: note *block_size must be in [4096, inf] here */
        // This assignment (because of the asserts below and the value above)
        // should be in the range [1,++] (as an over approximation)
        // The division should be : [4096,++] / [1,4096]
        *frames_per_block = *block_size/frame_size;		/* Goanna[ATH-div-0-unchk-param] Severity-Medium, Parameter `frame_size' is not checked against 0 before it is used as a divisor */
}

void
create_ring(pcap_t *handle)
{
        unsigned int       frames_per_block;
        struct tpacket_req req;

        req.tp_frame_size = TPACKET_ALIGN(handle->snapshot +
                                          TPACKET_ALIGN(handle->md.tp_hdrlen) +
                                          sizeof(struct sockaddr_ll));
	assert(req.tp_frame_size > 0);				/* Goanna: even asserting this does not silence the warning */
	assert(req.tp_frame_size <= 4096);			/* Goanna: even asserting this does not silence the warning */
        compute_ring_block(req.tp_frame_size, &req.tp_block_size, &frames_per_block);
        req.tp_block_nr = req.tp_frame_nr / frames_per_block;	/* Goanna[ATH-div-0-unchk-local] Severity-Medium, Local variable `frames_per_block' is not checked against 0 before it is used as a divisor */
}
