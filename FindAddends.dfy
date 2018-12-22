predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x

{
    i, j := 0, |q| - 1;
    ghost var i_result, j_result :|
            0 <= i_result < j_result < |q|
            && q[i_result] + q[j_result] == x;


    while Guard(q, x, i, j)
        invariant Inv(q, x, i, j, i_result, j_result)
        decreases j - i
    {
        if Guard2(q, x, i, j)
        {
            // For clarification see L1
            i := i + 1;
        }
        else
        {
            // L2 should be similar to L1
            j := j - 1;
        }

    }
}


lemma L1 (q : seq<int>, x: int, i: nat, j: nat, i_result:nat, j_result:nat)
    requires Inv(q, x, i, j, i_result, j_result)
    requires Guard2(q, x, i, j)
    requires Sorted(q) 
    requires q[i_result] + q[j_result] == x
    ensures Inv(q, x, i+1, j, i_result, j_result)
{
    // Guard2 + q[i_result] + q[j_result] == x  ==> i != i_result || j != j_result ==>
    // Invariant ==> i < i_result || j > j_result ==>
    // Negately assume i == i result, therefore j > j_result
    // Guard2 ==> q[i] + q[j] < x ==>
    // Sorted & j > j_result ==> q[i] + q[j_result] < q[i] + q[j] < x ==>
    // i == i_result ==> q[i_result] + q[j_result] < x. Contradiction.

    // Therefore, i < i_result 
}

predicate method Guard(q : seq<int>, x: int, i: nat, j: nat)
requires 0 <= i < j < |q|
{
    q[i] + q[j] != x
}

predicate method Guard2(q : seq<int>, x:int, i:nat, j:nat)
requires 0 <= i < j < |q|
{
    q[i] + q[j] < x
    }

predicate Inv(q : seq<int>, x: int, i: nat, j: nat, i_result:nat, j_result:nat){
    0 <= i < j < |q| 
    && 0 <= i_result < j_result < |q| 
    && i <= i_result
    && j >= j_result
}

method Main()
{
	var q := [1,2,4,5,6,7,10,23];
	assert Sorted(q);
	assert HasAddends(q,10) by { assert q[2]+q[4] == 4+6 == 10; }
	var i,j := FindAddends(q, 10);
	print "Searching for addends of 10 in q == [1,2,4,5,6,7,10,23]:\n";
	print "Found that q[";
	print i;
	print "] + q[";
	print j;
	print "] == ";
	print q[i];
	print " + ";
	print q[j];
	print " == 10";
	assert i == 2 && j == 4;
}