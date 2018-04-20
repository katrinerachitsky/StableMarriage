method Main() 
decreases *{
  
  var man0, man1, man2 := new int[3], new int[3], new int[3];
  man0[0], man0[1], man0[2] := 0,1,2;
  man1[0], man1[1], man1[2] := 0,2,1;
  man2[0], man2[1], man2[2] := 1,2,0;
  var woman0, woman1, woman2 := new int[3], new int[3], new int[3];
  woman0[0], woman0[1], woman0[2] := 1,0,2;
  woman1[0], woman1[1], woman1[2] := 2,1,0;
  woman2[0], woman2[1], woman2[2] := 1,0,2;
  var men: map<int, array<int>> := map[0 := man0, 1 := man1, 2 := man2];
  var women: map<int, array<int>> := map[0 := woman0, 1 := woman1, 2:= woman2];
  var results := matching(men, women);
  var i := 0;
  print "\n final matches are: \n";
  while (i < |results|) && i in results {
    print " woman ", i, " man ", results[i], "\n";
    i := i + 1;
  } /* solution is  woman 0 man 1, woman 1 man 2, woman 2 man 0*/
}

method matching(men: map<int, array<int>>, women: map<int, array<int>>) returns (matched_output: map<int, int>)
  decreases *
  requires |men| != 0
  requires |women| != 0
  requires |men| == |women|
  requires forall i :: 0 <= i < |men| ==> i in men && men[i] != null && men[i].Length == |women| && (forall j :: 0 <= j < men[i].Length ==> (men[i])[j] in women.Keys) 
  requires forall i :: 0 <= i < |women| ==> i in women && women[i] != null && women[i].Length == |men| && (forall j :: 0 <= j < women[i].Length ==> (women[i])[j] in men.Keys) 
  // ensures forall i :: 0 <= i < |men| ==> i in matched_output.Values;
  // ensures forall i :: 0 <= i < |women| ==> i in matched_output.Keys;
  {
    var matched: map<int,int>;
    var indexLastAttempted: map<int,int> := initMen(men.Keys);
    assert (forall i :: 0 <= i < |men.Keys| && i in men ==> i in indexLastAttempted && indexLastAttempted[i] == -1);
    var currentMan: int := getFreeMan(men.Keys, matched.Values);
    assert ((currentMan == |men.Keys - matched.Values| ==> forall i :: 0 <= i < |men.Keys - matched.Values| ==> i !in (men.Keys - matched.Values))  || (currentMan < |men.Keys - matched.Values| ==> currentMan in men.Keys - matched.Values));
    var currentPrefIndex: int;
    while (currentMan in men.Keys - matched.Values)
     decreases *
     invariant 0 <= |men.Keys - matched.Values|
     // invariant -1 <= indexLastAttempted[currentMan] <= |women|
     // decreases |women| - indexLastAttempted[currentMan]
    {
        var preferences: array := men[currentMan];
        if (currentMan in indexLastAttempted && 0 <= indexLastAttempted[currentMan] < (preferences.Length - 1)){
            currentPrefIndex := indexLastAttempted[currentMan];
            currentPrefIndex := currentPrefIndex + 1;
       } else {
          currentPrefIndex := 0;
       }
        while (currentPrefIndex < preferences.Length)
          invariant 0 <= currentPrefIndex <= preferences.Length
          // invariant -1 <= indexLastAttempted[currentMan] <= |women|
          decreases (preferences.Length - currentPrefIndex)
              {
              indexLastAttempted := indexLastAttempted[currentMan :=        currentPrefIndex];
              var currentWoman: int := preferences[currentPrefIndex];
              if (currentWoman !in matched.Keys) {               
                matched := matched[currentWoman := currentMan];
                break;
              } else if (currentWoman in matched.Keys && currentWoman in women) {
                    var preferences: array := women[currentWoman];
                    var man_matched: int := matched[currentWoman];           
                    var currentMan_index: int:= Find(preferences, currentMan);
                    var man_matched_index: int := Find(preferences, man_matched);                 
                    if (currentMan_index < man_matched_index) {
                      matched := map i | i in matched && i != currentWoman :: matched[i];
                      matched := matched[currentWoman := currentMan];                       
                      break;
                    }
              }
              currentPrefIndex := currentPrefIndex + 1;
              }
        currentMan := getFreeMan(men.Keys, matched.Values); 
        assert ((currentMan == |men| ==> forall i :: 0 <= i < |men.Keys| ==>     i !in men.Keys || i in matched.Values) || (currentMan < |men| ==>     currentMan in men.Keys && currentMan !in matched.Values));
    }
    // assert forall i :: 0 <= i < |men| ==> i in matched.Values;
    // assert forall i :: 0 <= i < |women| ==> i in matched.Keys;
    matched_output := matched;
    return matched_output;
}

method getFreeMan(men: set<int>, engagedMen: set <int>) returns (index: int) 
  requires |men| > 0;
  ensures index < |men - engagedMen| ==> index in men - engagedMen;
  ensures index == |men - engagedMen| ==> forall i :: 0 <= i < |men - engagedMen| ==> i !in (men - engagedMen);
  {
  index := 0;
  while (index < |men|)
  decreases |men| - index
  invariant 0 <= index <= |men|;
  invariant forall i :: 0 <= i < index ==> i !in (men - engagedMen)
  {
    if (index in (men - engagedMen)) {
      return index;
    } else {
      index := index + 1;
    }
  }
  }

method initMen(men: set<int>) returns (preferenceCounter: map<int,int>)
  requires |men| > 0
  requires forall i :: 0 <= i < |men| ==> i in men
  ensures forall i :: 0 <= i < |men| ==> i in preferenceCounter && i in men && preferenceCounter[i] == -1
{
  var index := 0;
  while (index < |men|)
  invariant 0 <= index <= |men|
  invariant forall i :: 0 <= i < index ==> i in preferenceCounter && i in men && preferenceCounter[i] == -1
  {
    preferenceCounter := preferenceCounter[index := -1];
    index := index + 1;
  }
}

method Find(a: array<int>, key: int) returns (index: int)
   requires a != null
   ensures 0 <= index ==> index < a.Length && a[index] == key
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
   index := 0;
   while index < a.Length
      invariant 0 <= index <= a.Length
      invariant forall k :: 0 <= k < index ==> a[k] != key
   {
      if a[index] == key { return; }
      index := index + 1;
   }
   index := -1;
}