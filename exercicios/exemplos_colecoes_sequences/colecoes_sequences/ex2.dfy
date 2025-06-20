method Main()
{
    var a := new int[5];
    a[0] := 0;
    a[1] := 1;
    a[2] := 2;
    a[3] := 3;
    a[4] := 4;
    
    assert a[..] == [0,1,2,3,4]; //conversão de array para seq
    assert a[1..3] == [1,2]; //conversão de sub-array para seq
    assert a[2..] == [2,3,4]; //"drop" conversão de sub-array para seq
    assert a[..2] == [0,1]; //"take" conversão de sub-array para seq

    assert forall i :: 0 <= i < a.Length ==> a[i] != 10;
    assert 10 !in a[..]; //elemento 10 não está no array

    //assert a[3] == 3;
    //A seguinte asserção necessita de um "lembrete" explícito do conteúdo do array para ser provada.
    //O problema é a regra de "introdução do existencial" que precisa conhecer um valor para i em a[i]
    assert exists i :: 0 <= i < a.Length && a[i] == 3; 
    assert 3 in a[..]; //elemento 3 está no array
}