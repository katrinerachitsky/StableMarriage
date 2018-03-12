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
    print " woman ";
    print i;
    print " man ";
    print results[i];
    print "\n";
    i := i + 1;
  }*/ /* solution is man 0, woman 0, man 1 woman 1 man 2 woman 2 */

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
    print " woman ";
    print i;
    print " man ";
    print results[i];
    print "\n";
    i := i + 1;
  }*/ /*solution is man 0 woman 2, man 1 woman 3, man 2 woman 0, man 3 woman 1*/
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
    print " woman ";
    print i;
    print " man ";
    print results[i];
    print "\n";
    i := i + 1;
  } /* solution is  woman 0 man 1, woman 1 man 2, woman 2 man 0*/
}

method matching(men: map<int, array<int>>, women: map<int, array<int>>) returns (matched_output: map<int, int>)  // matched array is a mapping of women to their respective mate
  // require each person on preference list to be in the women keys mapping, and vice versa for men
  decreases *;
  requires |men| != 0; // requires cardinality of men map to be non-zero
  requires |women| != 0;
  requires |men| == |women| // requires cardinality of men and women maps to be equal
  //requires 0 in men && 0 in women; // both men and women need to start at 0 (man 0 and woman 0)
  //requires -1 !in men && -1 !in women; // requires no negative numbers
  requires forall i :: 0 <= i < |men| ==> i in men && men[i] != null && men[i].Length == |men| // checks that for each possible key in domain, this key exists in the mapping, that the array (value) associated with this key is non-empty and that it contains exactly the amount of entries as each map (the domain)
  requires forall i :: 0 <= i < |women| ==> i in women && women[i] != null && women[i].Length == |women| // checks the same for women's list
  //ensures |matched_output| == |men|
  //ensures forall i :: 0 <= i < |women| ==> i in matched_output.Keys;
  //ensures forall i :: 0 <= i < |men| ==> i in matched_output.Values;
  //ensures forall i :: 0 <= i < domain ==> i in matched && exists j :: 0 <= j < domain && matched[i] == j // ensures that the resulting matching includes all original participants (everyone has a match)
  {
    
    var matched: map<int,int>;
    var indexLastAttempted: map<int,int>;
    var currentMan: int := getFreeMan(men.Keys, matched.Values); // calls getFreeMan to find first man from set of men and finds a man not in the matched values yet
    var couplesMatched: int := 0;
    while (couplesMatched < |men| && currentMan in men.Keys && currentMan !in matched.Values) // while cardinality of matched is less than that of men
      invariant 0 <= couplesMatched <= |men|
      //invariant couplesMatched <= |matched|
      // having problems proving that on every iteration decreases, because it doesn't
      // sometimes the amount of people matched stays the same
      // so how do we prove termination?
      // we know they stay the same sometimes because a better match is found, and one man gets taken off the matched list to get re-matched

      //decreases (|men| - |matched|);
      decreases *;
    {
        var preferences: array := men[currentMan]; // get preference list for current man
        var currentPrefIndex: int := 0; // set current woman to top of preference list (so that we immediately go for highest ranking woman on currentMan's list)
        while (currentPrefIndex < preferences.Length) // while we have not reached the end of the preferences list
          invariant 0 <= currentPrefIndex <= preferences.Length
          //invariant couplesMatched <= |matched|
          //invariant forall i :: 0 <= i < preferences.Length ==> preferences[i] in women
          //invariant forall i :: 0 <= i < currentPrefIndex ==> (preferences[currentPrefIndex]) in matched.Keys
          decreases (preferences.Length - currentPrefIndex)
        {
          
          if (currentMan !in indexLastAttempted || currentPrefIndex > indexLastAttempted[currentMan]){ // if this index in the preference list has already been attempted
            /*if (currentPrefIndex <= indexLastAttempted[currentMan]){
             print "man ";
            print currentMan;
            print " could've skipped this woman at index ";
            print currentPrefIndex;
            print ", he's already been left by her\n";
            //}
            print "the last index attempted of man ";
            print currentMan;
            print " was ";
            print indexLastAttempted[currentMan];
            print "\n";
            print "man ";
            print currentMan;
            print " has last attempted to marry woman at index ";
            print indexLastAttempted[currentMan];
            print "\n";*/
            indexLastAttempted := indexLastAttempted[currentMan := currentPrefIndex];
          print "man ";
           print currentMan;
          print" is currently trying to marry woman at index ";
          print currentPrefIndex;
          print "\n";
          var currentWoman: int := preferences[currentPrefIndex]; // starting at index 0 of preferences list, highestPreferred woman will be named first
          print" which is woman ";
          print currentWoman;
          print "\n";
          if (currentWoman !in matched.Keys && currentWoman in women) { // if the highestPreferred woman is not found in the matched mapping == if highest preferred woman free
            matched := matched[currentWoman := currentMan]; // add current highestpreferred woman and current man to mapping
            //couplesMatched := couplesMatched + 1;
            print "  man ";
            print currentMan;
            print " and woman ";
            print currentWoman;
            print " engaged\n";
            break;
          } else if (currentWoman in matched.Keys && currentWoman in women) { // if current woman is matched
            var preferences: array := women[currentWoman]; // get woman's preference list
            var man_matched: int := matched[currentWoman]; // find woman's current mate
            var currentMan_index: int:= Find(preferences, currentMan); // get index on preference list of woman for current man
            var man_matched_index: int := Find(preferences, man_matched); // get index on preference list of woman for current mate
            if (currentMan_index < man_matched_index) { // if index of current man is higher on preference list than the matched mate
              matched := map i | i in matched && i != currentWoman :: matched[i]; // remove original woman-man pair from matched
              couplesMatched := couplesMatched - 1;
              matched := matched[currentWoman := currentMan]; // add current Man with his highestpreferred woman to mapping
              print "  man ";
              print currentMan;
              print " and woman ";
              print currentWoman;
              print " engaged, she left man ";
              print man_matched;
              print "\n";
              //couplesMatched := couplesMatched + 1;
              break;
            }
          }
            
          }

          
        /*print "man ";
              print currentMan;
              print " and woman ";
              print currentWoman;
              print " not engaged, she preferred her current partner ";
              print "\n";*/
        currentPrefIndex := currentPrefIndex + 1; // move on to the next woman for next iter of while loop
      }
      couplesMatched := couplesMatched + 1;
      // man should be matched by this point
      currentMan := getFreeMan(men.Keys, matched.Values); // calls getFreeMan to find first man from set of men and finds a man not in the matched values yet
      /*if (|matched| == |men|){
        assert (currentMan in men.Keys && currentMan !in matched.Values); 
      }*/
    } // end of men needing a match
    matched_output := matched;
    return matched_output;
}

method getFreeMan(men: set<int>, engagedMen: set <int>) returns (index: int) 
  requires |men| > 0;
  ensures index < |men| ==> index in men && index !in engagedMen;
  ensures index >= |men| ==> forall i :: 0 <= i < |men| ==> i !in men || i in engagedMen; // if index is larger than or equal to cardinality of men, all i from 0 to cardinality of men must either be in engagedMen or not in men at all
  {
  index := 0;
  while (index < |men|)
  decreases |men| - index
  invariant 0 <= index <= |men|;
  invariant forall i :: 0 <= i < index ==> i !in men || i in engagedMen // for any i less than the current index, we know either that i must not be in men OR that i is already in engagedMen
  {
    if (index in men && index !in engagedMen)
    {
      return index;
    } else {
      index := index + 1;
    }
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

method createIndexMap(men: set<int>) returns (initialized: map<int,int>)
  requires |men| > 0;
  requires forall i :: 0 <= i < |men| ==> i in men
  ensures forall i :: 0 <= i < |men| ==> i in initialized && initialized[i] == 0
{
   var index := 0;
   while (index < |men|)
    decreases |men| - index
    invariant 0 <= index <= |men|
    invariant forall i :: 0 <= i < index ==> i in initialized && initialized[i] == 0
   {
     initialized := initialized[index := 0];
     index := index + 1;
   }
}