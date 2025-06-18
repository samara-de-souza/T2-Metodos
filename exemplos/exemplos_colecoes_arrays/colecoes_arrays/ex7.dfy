method CriarZerado(n:nat) returns (a:array<int>)
  requires n > 0
  ensures a.Length == n
  //ensures fresh(a) //sem essa cláusula, a verificação falha no método Main
  ensures forall i :: 0 <= i < a.Length ==> a[i] == 0
{
  a := new int[n];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == 0
  {
    a[i] := 0;
    i := i + 1;
  }
}

method Main()
{
  var a := CriarZerado(5);
  var v := a[3];
  assert v == 0;
  a[0] := 1;
}
