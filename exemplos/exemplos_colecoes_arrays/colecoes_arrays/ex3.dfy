method Main()
{
    var a := new int[5];
    //incializar todas posições em 0
    forall i | 0 <= i < a.Length
    {
        a[i] := 0;
    }
    var v := a[3];
    assert v == 0;
}