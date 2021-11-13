void copy_subarray(uint8 *out, const uint8 *in, 
		uint32 len, uint32 l_idx, uint32 sub_len){
	uint32 i,j;
	for(i=0,j=0; i<len; i++){
		if((i >= l_idx) && (i<l_idx + sub_len)){
			out[j] = in[i];
			j++;
		}
	}
}