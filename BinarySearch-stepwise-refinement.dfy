predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate Inv(q: seq<int>, key: int, i: nat, j: nat, k: nat)
{
	i <= j < k <= |q| 
	&& key in q[i..k]
}


method {:verify true} BinarySearch(q: seq<int>, key: int) returns (j: nat)
	requires Sorted(q) && key in q
	ensures j < |q| && q[j] == key
	{
		//introduce locals 
		var i: nat, k : nat;
		i, j, k := BinarySearch2(q, key);
	}

method {:verify true} BinarySearch2(q: seq<int>, key: int) returns (i:nat, j: nat, k:nat )
	requires Sorted(q)
	requires key in q
	ensures j < |q| 
	ensures q[j] == key
{
	// Sequential composition1
	i, j, k := Init(q, key);
	i, j, k := Iteration (q, key, i, j, k);

	L1(q, key, i, j, k);
}


method {:verify true} Init(q: seq<int>, key: int) returns (i:nat, j: nat, k:nat )
	requires Sorted(q) 
	requires key in q
	ensures Sorted(q)
	ensures Inv(q, key, i, j, k)

	{
		// weaken precondition
		i, j, k := InitIJK(q, key);
	}


method {:verify true} InitIJK(q: seq<int>, key: int) returns (i: nat, j:nat, k:nat)
	//requires Sorted(q) 
	requires key in q
	ensures Inv(q, key, i, j, k)
{
	// leading Assignment
	i, k := InitIK(q, key);
	j := UpdateJ(i, k);
}

method InitIK (q: seq<int>, key:int )returns (i:nat, k:nat)
requires key in q
ensures i < k <= |q|
ensures key in q[i..k]
{
	// Assignment
	i := 0;
	k := |q|;
}



method {:verify true} UpdateJ (i:nat, k:nat) returns (j : nat)
requires i < k
ensures i <= j < k
{	
	//Assignment
	j := (i + k) / 2;
}


method Iteration(q: seq<int>, key: int, i0: nat, j0: nat, k0: nat) returns (i:nat, j: nat, k : nat)
	requires Inv(q, key, i0, j0, k0)
	requires Sorted(q)
	ensures Inv(q, key, i, j, k)
	ensures q[j] == key
{
	i, j, k := i0, j0, k0;
	while q[j] != key
		invariant Inv(q, key, i, j, k)
		decreases V(i, k)
		{
			i, j, k := LoopBody(q, key, i, j ,k);
		}

}

lemma L1(q: seq<int>, key: int, i : nat, j:nat, k:nat)
requires Inv(q, key, i, j, k)
requires q[j] == key
ensures j < |q|
ensures q[j] == key
{
	
}

method LoopBody(q: seq<int>, key: int, i0: nat, j0: nat, k0: nat) returns (i :nat, j: nat, k:nat)
requires Sorted(q)
requires Inv(q, key, i0, j0, k0)
requires Guard1(q, key, j0) // q[j0] != key
ensures Inv(q, key, i, j, k)
ensures k0 - i0 > k - i 
ensures j < |q|
{
	// Alternate
	if Guard2(q, key, j0)
	{
		updateILemma(q, key, i0, j0, k0);
		i := UpdateI(q, key, i0, j0, k0);
		k := k0;
	}
	else
	{
		updateKLemma(q, key, i0, j0, k0);
		k := UpdateK(q, key, i0, j0, k0);
		i := i0;
	}

	// Assignment
	j:= (k + i) / 2;
}


predicate method Guard1(q: seq<int>, key: int, j: nat)
requires 0 <= j < |q|
{
	q[j] != key
}

function V(i: nat, k: nat): int
{
	k - i
}

predicate method Guard2(q: seq<int>, key: int, j: nat)
requires j < |q|
{
	q[j] < key
}

method UpdateI(q: seq<int>, key: int, i0: nat, j: nat, k: nat) returns (i: nat)
requires Sorted(q)
requires j + 1 < k
requires Inv(q, key, i0, j, k)
requires q[j] < key
ensures i > i0
ensures k > i
ensures key in q[i..k]
{
	i := j + 1;
}

method UpdateK(q: seq<int>, key: int, i: nat, j: nat, k0: nat) returns (k: nat)
requires Inv(q, key, i, j, k0)
requires Sorted(q)
requires q[j] > key
requires j > i
ensures k0 > k > i
ensures key in q[i..k]
{
	k := j;
}

lemma updateILemma(q: seq<int>, key: int, i: nat, j: nat, k: nat)
requires Inv(q, key, i, j, k)
requires q[j] < key
requires Sorted(q)
ensures j + 1 < k
{
}

lemma updateKLemma(q: seq<int>, key: int, i: nat, j: nat, k: nat)
requires Inv(q, key, i, j, k)
requires q[j] > key
requires Sorted(q)
ensures i < j
{
}

method Main()
{
	var q := [1,2,4,5,6,7,10,23];
	assert Sorted(q);
	assert 10 in q;
	var i := BinarySearch(q, 10);
	print "[1,2,4,5,6,7,10,23][";
	print i;
	print "] == 10";
	assert i == 6;
}