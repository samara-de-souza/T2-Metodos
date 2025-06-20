ghost function to_seq<T>(a: array<T>, i: int) : (res: seq<T>)
  requires 0 <= i <= a.Length
  ensures res == a[i..]
  reads a
  decreases a.Length-i
{
  if i == a.Length
  then []
  else [a[i]] + to_seq(a, i + 1)
}

method Main() {
  var a: array<int> := new int[3];
  a[0] := 2;
  a[1] := 3;
  a[2] := 1;

  var ms: multiset<int> := multiset(a[..]);
  assert a[..] == to_seq(a, 0); //dica para o Dafny
  assert ms[2] == 1;
  assert ms[0] == 0;
}