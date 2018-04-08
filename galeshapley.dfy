method Main() 
decreases *{
  
  /*test 1*/
  /*
  var man0, man1, man2 := new int[3], new int[3], new int[3] ;
  man0[0], man0[1], man0[2] := 0, 1, 2;
  man1[0], man1[1], man1[2] := 1, 0, 2;
  man2[0], man2[1], man2[2] := 0, 1, 2;
  var woman0, woman1, woman2 := new int[3], new int[3], new int[3] ;
  woman0[0], woman0[1], woman0[2] := 1, 0, 2;
  woman1[0], woman1[1], woman1[2] := 0, 1, 2;
  woman2[0], woman2[1], woman2[2] := 0, 1, 2;

  var men: map<int, array<int>> := map[0 := man0, 1 := man1, 2 := man2];
  var women: map<int, array<int>> := map[0 := woman0, 1 := woman1, 2:= woman2];
  var results := matching(men, women);

  var i := 0;
  print "\n final matches are: \n";
  while (i < |results|) && i in results {
     print " woman ", i, " man ", results[i], "\n";
    i := i + 1;
  } */ /* solution is man 0, woman 0, man 1 woman 1 man 2 woman 2 */

  /*test 2*/
  /*
  var man0, man1, man2, man3 := new int[4], new int[4], new int[4], new int[4] ;
  man0[0], man0[1], man0[2], man0[3] := 2,3,1,0;
  man1[0], man1[1], man1[2], man1[3] := 3,2,0,1;
  man2[0], man2[1], man2[2], man2[3] := 0,2,1,3;
  man3[0], man3[1], man3[2], man3[3] := 1,3,0,2;

  var woman0, woman1, woman2, woman3 := new int[4], new int[4], new int[4], new int[4] ;
  woman0[0], woman0[1], woman0[2], woman0[3] := 3,0,1,2;
  woman1[0], woman1[1], woman1[2], woman1[3] := 2,1,0,3;
  woman2[0], woman2[1], woman2[2], woman2[3] := 2,1,0,3;
  woman3[0], woman3[1], woman3[2], woman3[3] := 3,0,1,2;

  var men: map<int, array<int>> := map[0 := man0, 1 := man1, 2 := man2, 3 := man3];
  var women: map<int, array<int>> := map[0 := woman0, 1 := woman1, 2:= woman2, 3 := woman3];
  var results := matching(men, women);
  var i := 0;
  print "\n final matches are: \n";
  while (i < |results|) && i in results {
     print " woman ", i, " man ", results[i], "\n";
    i := i + 1;
  }*/ /*solution is woman 0 man 2, woman 1 man 3, woman 2 man 0, woman 3 man 1*/
  /*test 3*/
  
  var man0, man1, man2 := new int[3], new int[3], new int[3] ;
  man0[0], man0[1], man0[2] := 0, 1, 2;
  man1[0], man1[1], man1[2] := 0,2,1;
  man2[0], man2[1], man2[2] := 1,2,0;
  var woman0, woman1, woman2 := new int[3], new int[3], new int[3] ;
  woman0[0], woman0[1], woman0[2] := 1, 0, 2;
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
  //assert (forall i :: 0 <= i < |results| && i in results.Keys && i in women);
  //assert forall i :: 0 <= i < |results| ==> i in results.Values && i in men;
}

method matching(men: map<int, array<int>>, women: map<int, array<int>>) returns (matched_output: map<int, int>)  // matched array is a mapping of women to their respective mate
  // require each person on preference list to be in the women keys mapping, and vice versa for men
  decreases *;
  requires |men| != 0; // requires cardinality of men map to be non-zero
  requires |women| != 0;
  requires |men| == |women| // requires cardinality of men and women maps to be equal
  requires forall i :: 0 <= i < |men| ==> i in men && men[i] != null && men[i].Length == |women| // checks that for each possible key in domain, this key exists in the mapping, that the array (value) associated with this key is non-empty and that it contains exactly the amount of entries as each map (the domain)
  requires forall i :: 0 <= i < |women| ==> i in women && women[i] != null && women[i].Length == |men| // checks the same for women's list
  
  {
    var matched: map<int,int>;
    var indexLastAttempted: map<int,int> := initMen(men.Keys);
    //var indexLastAttempted: map<int,int>;
    assert (forall i :: 0 <= i < |men.Keys| ==> i in indexLastAttempted && i in men && indexLastAttempted[i] == -1);
    var currentMan: int := getFreeMan(men.Keys, matched.Values); // calls getFreeMan to find first man from set of men and finds a man not in the matched values yet
    //indexLastAttempted := indexLastAttempted[currentMan := -1];
    //assert currentMan in indexLastAttempted;
    assert ((currentMan == |men.Keys - matched.Values| ==> forall i :: 0 <= i < |men.Keys - matched.Values| ==> i !in (men.Keys - matched.Values)) || (currentMan < |men.Keys - matched.Values| ==> currentMan in men.Keys - matched.Values));
    var currentPrefIndex: int;
    var freeMen : set<int> := men.Keys - matched.Values;
    
    while (men.Keys - matched.Values != {} && currentMan in men && currentMan in indexLastAttempted && indexLastAttempted[currentMan] < men[currentMan].Length) // while the set of men who are not engaged yet is not empty
      //decreases men[currentMan].Length - indexLastAttempted[currentMan]
      decreases *
      invariant 0 <= |men.Keys - matched.Values|
      //invariant currentMan in indexLastAttempted
      //invariant 0 <= currentMan <= |men|
    {
      //assert currentMan in indexLastAttempted;
        var preferences: array := men[currentMan]; // get preference list for current man
        if (0 <= indexLastAttempted[currentMan] < (preferences.Length - 1)){
          currentPrefIndex := indexLastAttempted[currentMan]; // set currentPrefIndex to the index this man tried last on his pref list
          currentPrefIndex := currentPrefIndex + 1; // incremement so we go on to the next woman (don't repeat a proposal)
        } else {
          currentPrefIndex := 0; // if indexLastAttempted not defined for currentMan, means this is the first time the man is proposing, so start at beginning of pref list (index 0)
        }
        while (currentPrefIndex < preferences.Length) // while we have not reached the end of the preferences list
          invariant 0 <= currentPrefIndex <= preferences.Length
          
          //invariant (currentMan !in indexLastAttempted || currentPrefIndex <= indexLastAttempted[currentMan] < preferences.Length)
          // for each woman before the currentone, she has preferred somebody else
          //invariant forall i :: 0 <= i < currentPrefIndex ==> preferences[i] in matched
          //invariant (preferences[currentPrefIndex] !in matched.Keys ||  )
          decreases (preferences.Length - currentPrefIndex) // means that our amount of women gets smaller accross each iteration, loop terminates when we've exhausted all preferences on a man's list
        {
          indexLastAttempted := indexLastAttempted[currentMan := currentPrefIndex];
          var currentWoman: int := preferences[currentPrefIndex]; // starting at index 0 of preferences list, highestPreferred woman will be named first
          if (currentWoman !in matched.Keys && currentWoman in women) { // if the highestPreferred woman is not found in the matched mapping == if highest preferred woman free
            matched := matched[currentWoman := currentMan]; // add current highestpreferred woman and current man to mapping
            break;
          } else if (currentWoman in matched.Keys && currentWoman in women) { // if current woman is matched
            var preferences: array := women[currentWoman]; // get woman's preference list
            var man_matched: int := matched[currentWoman]; // find woman's current mate
            var currentMan_index: int:= Find(preferences, currentMan); // get index on preference list of woman for current man
            var man_matched_index: int := Find(preferences, man_matched); // get index on preference list of woman for current mate
            if (currentMan_index < man_matched_index) { // if index of current man is higher on preference list than the matched mate
              matched := map i | i in matched && i != currentWoman :: matched[i]; // remove original woman-man pair from matched
              matched := matched[currentWoman := currentMan]; // add current Man with his highestpreferred woman to mapping
              break;
            }
          }
        currentPrefIndex := currentPrefIndex + 1; // move on to the next woman for next iter of while loop
      }
      // man should be matched by this point
      currentMan := getFreeMan(men.Keys, matched.Values); // calls getFreeMan to find first man from set of men and finds a man not in the matched values yet
      assert ((currentMan == |men| ==> forall i :: 0 <= i < |men.Keys| ==> i !in men.Keys || i in matched.Values) || (currentMan < |men| ==> currentMan in men.Keys && currentMan !in matched.Values)); // making sure that the next man chosen from the method call above is not yet engaged
    } // end of men needing a match
    /*var noman := getFreeMan(men.Keys, matched.Values);
    assert (noman == |men| ==> forall i :: 0 <= i < |men.Keys| ==> i !in men.Keys || i in matched.Values);*/
    //assert (men.Keys - matched.Values == {});
    // loop has been exited
    // which means getFreeMan returned an index larger than |men|
    matched_output := matched;
    return matched_output;
}

method getFreeMan(men: set<int>, engagedMen: set <int>) returns (index: int) 
  requires |men| > 0;
  ensures index < |men - engagedMen| ==> index in men - engagedMen;
  ensures index == |men - engagedMen| ==> forall i :: 0 <= i < |men - engagedMen| ==> i !in (men - engagedMen); // if index is larger than or equal to cardinality of men, all i from 0 to cardinality of men must either be in engagedMen or not in men at all
  {
  index := 0;
  while (index < |men|)
  decreases |men| - index
  invariant 0 <= index <= |men|;
  invariant forall i :: 0 <= i < index ==> i !in (men - engagedMen) // for any i less than the current index, we know either that i must not be in men OR that i is already in engagedMen
  {
    if (index in (men - engagedMen))
    {
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

method Find(a: array<int>, key: int) returns (index: int) // found on website, takes an array a with a key int and returns the index at which the key appears in the array
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