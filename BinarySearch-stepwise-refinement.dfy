predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

method BinarySearch(q: seq<int>, key: int) returns (j: nat)
	requires Sorted(q) && key in q
	ensures j < |q| && q[j] == key

predicate Inv(q: seq<int>, key: int, i: nat, j: nat, k: nat)

predicate method Guard1(q: seq<int>, key: int, j: nat)

method Init(q: seq<int>, key: int) returns (i: nat, j: nat, k: nat)

function V(i: nat, k: nat): int

predicate method Guard2(q: seq<int>, key: int, j: nat)

method UpdateI(q: seq<int>, key: int, i0: nat, j: nat, k: nat) returns (i: nat)

method UpdateK(q: seq<int>, key: int, i: nat, j: nat, k0: nat) returns (k: nat)

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