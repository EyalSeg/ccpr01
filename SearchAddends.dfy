predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q)
    requires HasAddends(q, x)
	ensures  i < j < |q| && q[i]+q[j] == x
{
    // Introduce logical constants
        ghost var i_result, j_result :|
            0 <= i_result < j_result < |q|
            && q[i_result] + q[j_result] == x;
    //Assignment
    i, j := FindAddends_WithLogicalConstants(q, x, i_result, j_result);
}

method {:verify true} FindAddends_WithLogicalConstants(q: seq<int>, x: int, ghost i_result : nat, ghost j_result:nat) returns(i: nat, j:nat)
requires Sorted(q)
requires HasAddends(q, x)
requires 0 <= i_result < j_result < |q|
requires q[i_result] + q[j_result] == x
ensures i < j < |q| && q[i] + q[j] == x
{
    // Sequential composition
    i, j := Init(q, x, i_result, j_result);
    Lemma_init(q, x, i, j, i_result, j_result);
    i, j := Iterate(q, x, i, j, i_result, j_result);
}

method {:verify true} Init(q: seq<int>, x : int, ghost i_result:nat, ghost j_result:nat ) returns (i:nat, j:nat)
requires Sorted(q)
requires HasAddends(q, x)
requires 0 <= i_result < j_result < |q|
requires q[i_result] + q[j_result] == x
ensures  0 <= i <= j < |q|
ensures i <= i_result
ensures j_result <= j
ensures Sorted(q)
ensures  0 <= i_result < j_result < |q|
ensures q[i_result] + q[j_result] == x
{     
    i, j := 0, |q| - 1;
}

lemma Lemma_init(q: seq<int>, x : int, i : nat, j:nat, i_result:nat, j_result:nat )
requires  0 <= i <= j < |q|
requires i <= i_result
requires j_result <= j
requires Sorted(q)
requires 0 <= i_result < j_result < |q|
requires q[i_result] + q[j_result] == x
ensures Inv(q, x, i, j, i_result, j_result)
{

}

method {:verify true} Iterate (q: seq<int>,x: int, i0:nat , j0 :nat, ghost i_result:nat, ghost j_result:nat ) returns (i:nat, j:nat)
requires Inv(q, x, i0, j0, i_result, j_result)
ensures Inv(q, x, i, j, i_result, j_result)
ensures q[i] + q[j] == x
{
    i, j := i0, j0;
    while q[i] + q[j] != x
        invariant Inv(q, x,i, j, i_result, j_result)
        decreases j - i
        {
            i, j := LoopBody(q, x, i, j, i_result, j_result);
        }
}
method {:verify true} LoopBody(q: seq<int>, x : int, i0 : nat, j0: nat, ghost i_result:nat, ghost j_result:nat) returns (i : nat, j:nat)
requires Inv(q, x, i0, j0, i_result, j_result)
requires q[i0] + q[j0] != x
ensures Inv(q, x, i, j, i_result, j_result)
ensures (j0 - i0) > (j - i)
{
    if (q[i0] + q[j0] < x)
    {
        i, j := IncI(q, x, i0, j0, i_result, j_result);
    }
    else // q[i0] + q[j0] > x
    {
        i, j := DecJ(q, x, i0, j0, i_result, j_result);
    }

}

method {:verify true} IncI(q: seq<int>, x : int, i0 : nat, j0: nat, ghost i_result:nat, ghost j_result:nat) returns (i : nat, j:nat)
requires Inv(q, x, i0, j0, i_result, j_result)
requires q[i0] + q[j0] < x
ensures Inv(q,x, i, j, i_result, j_result)
ensures (j0 - i0) > (j - i)
{
    IncI_Lemma(q, x, i0, j0, i_result, j_result);
    i, j := i0 + 1, j0;
}

method {:verify true} DecJ(q: seq<int>, x : int, i0 : nat, j0: nat, ghost i_result:nat, ghost j_result:nat) returns (i : nat, j:nat)
requires Inv(q, x, i0, j0, i_result, j_result)
requires q[i0] + q[j0] > x
ensures Inv(q, x, i, j, i_result, j_result)
ensures (j0 - i0) > (j - i)
{
    DecJ_Lemma(q, x, i0, j0, i_result, j_result);
    i, j := i0, j0 - 1;
}

lemma DecJ_Lemma(q: seq<int>, x : int, i0 : nat, j0: nat, i_result:nat, j_result:nat)
requires Inv(q, x, i0, j0, i_result, j_result)
requires q[i0] + q[j0] > x
ensures j0 - 1 >= j_result
{

}

lemma IncI_Lemma (q: seq<int>, x : int, i0 : nat, j0: nat, i_result:nat, j_result:nat)
requires Inv(q, x, i0, j0, i_result, j_result)
requires q[i0] + q[j0] < x
ensures i0 + 1 <= i_result
{

}

predicate Inv(q:seq<int>, x:int, i:nat, j:nat, i_result:nat, j_result:nat)
{
    Sorted(q) 
    && 0 <= i_result < j_result < |q|
    && q[i_result] + q[j_result] == x
    && 0 <= i <= j < |q|
    && i <= i_result
    && j_result <= j
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