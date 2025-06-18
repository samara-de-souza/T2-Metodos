ghost predicate OrdenadoCrescente(a:array<int>)
  reads a
{
    forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

ghost predicate OrdenadoCrescenteSeq(a:seq<int>)
{
    forall i,j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

ghost predicate Permutacao(a:seq<int>, b:seq<int>)
{
    multiset(a) == multiset(b)
}

ghost predicate PontoDeQuebraEmOrdem(a:array<int>, n:int)
  requires 0 <= n <= a.Length
  reads a
{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

method SelectionSort(a:array<int>)
  modifies a
  ensures OrdenadoCrescenteSeq(a[..])
  ensures Permutacao(a[..], old(a[..]))
{
    var n := 0;
    while n < a.Length
      invariant 0 <= n <= a.Length
      invariant OrdenadoCrescenteSeq(a[..n])
      invariant Permutacao(a[..], old(a[..]))
      invariant PontoDeQuebraEmOrdem(a,n)
    {
        var mindex, m := n, n+1;
        while m < a.Length
          invariant n <= mindex < m <= a.Length
          invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
        {
            if a[m] < a[mindex]
            {
                mindex := m;
            }
            m := m + 1;
        }
        a[n], a[mindex] := a[mindex], a[n];
        n := n + 1;
    }
}

method FindMinIndex(a:array<int>, s:int) returns (mindex:int)
  requires a.Length > 0
  requires 0 <= s < a.Length
  ensures s <= mindex < a.Length
  ensures forall i :: s <= i < a.Length ==> a[mindex] <= a[i]
{
    var index := s + 1;
    mindex := s;
    while index < a.Length
      invariant s <= mindex < index <= a.Length
      //invariant s <= index <= a.Length
      //invariant s <= mindex < a.Length
      invariant forall j :: s <= j < index ==> a[mindex] <= a[j]
    {
        if a[index] < a[mindex]
        {
            mindex := index;
        }
        index := index + 1;
    }
}

method SelectionSortV2(a:array<int>)
  modifies a
  ensures OrdenadoCrescenteSeq(a[..])
  ensures Permutacao(a[..], old(a[..]))
{
    var n := 0;
    while n < a.Length
      invariant 0 <= n <= a.Length
      invariant OrdenadoCrescenteSeq(a[..n])
      invariant Permutacao(a[..], old(a[..]))
      invariant PontoDeQuebraEmOrdem(a,n)
    {
        var mindex := FindMinIndex(a,n);
        a[n], a[mindex] := a[mindex], a[n];
        n := n + 1;
    }
}

method Main()
{
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 10, 1, 0, 5;
  assert a[..] == [10,1,0,5];
  SelectionSort(a);
  assert a[..] == [0,1,5,10];
}