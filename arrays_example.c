//ORIGINAL CODE

int p(int x, int *data)
//@ requires data $\mapsto$ _; 
//@ ensures data $\mapsto$ _;
{
	return x + *data;
}

void array_map(int n[], int *data, int L)
//@ requires n $\mapsto$ [_]_L &*& data $\mapsto$ _;
//@ ensures n $\mapsto$ [_]_L &*& data $\mapsto$ _;
{
	if (L == 0) {
		skip;
	} else {
		//@ split n[0];
		int newVal  = p(n[0], data);
		n[0] =  newVal;
		array_map(n+1, data);
		//@ join n (n+1);
	}
	return;

} 

//TRANSLATED CODE

{int,int*} p_stub(int x, intptr_t data_addr, int* data_cap){
	intptr_t cap_address = (intptr_t) data_cap;
	
	{bool result, int* capability} = p(x,data_addr,data_cap);
	
	assert(cap_address == (intptr_t) capability);
	assert(is_linear(capability));
	
	return {result, capability};
}

{int,int*} p(int x, intptr_t data_address, int* data_cap)
{
	return {x + *data, data_cap};
}

{int[], int*} array_map(intptr_t n_addr, intptr_t data_addr, int L, int n_cap[], int* data_cap){
	assert(n_addr == (intptr_t) n_cap);
	assert(data_addr == (intptr_t) data_cap);
	assert(len(n_cap) == L);
	assert(is_linear(n_cap));
	assert(is_linear(data_cap));

	return array_map_old(n_addr, data_addr, n_cap, data_cap);
}

{int[], int*} array_map_old(int n_addr, int data_addr, int L, int n_cap[], int* data_cap) 
//Q: C does not allow returning  arrays like this... for historical reasons (https://stackoverflow.com/questions/26265489/why-can-c-functions-not-return-arrays)
//A: ignore this fact? Does verifast see the difference between heap and stack allocated pointers? 
{
	if (L == 0) {
		skip;
	} else {
		{n_cap0,n_cap1} = split(n,0);
		int newVal = p(n_cap0[0], data_addr, data_cap);
		n_cap0[0] = newVal;
		{n_cap1,data_cap} = array_map(n_cap1, data_cap);
		n_cap = join(n_cap0, n_cap1);
	}
	return {n_cap, data_cap};
} 