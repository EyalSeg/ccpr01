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
        if  q[i] + q[j] < x
        {

            i := i + 1;
        }
        else
        {

            j := j - 1;
        }

    }
}

predicate method Guard(q : seq<int>, x: int, i: nat, j: nat)
requires 0 <= i < j < |q|
{
    q[i] + q[j] != x
}

predicate Inv(q : seq<int>, x: int, i: nat, j: nat, i_result:nat, j_result:nat){
    0 <= i < j < |q| 
    && i <= i_result
    && j >= j_result
    //forall i0, j0 :: 0 <= i0 < i < j < j0 < |q| ==> q[i0] + q[j0] != x
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