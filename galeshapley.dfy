method matching(men: map<int, array<int>>, women: map<int, array<int>>, domain: int) returns (matched: map<int, int>)  // matched array is a mapping of women to their respective mate
  requires !(men.Items == {}) && 0 in men; // requires that the set of items in the map is non-empty
  requires !(women.Items == {}) && 0 in women; 
  requires |men| != 0;
  requires forall i :: 0 <= i < domain ==> i in men && men[i] != null && men[i].Length == domain // checks that for each possible key in domain, this key exists in the mapping, that the array (value) associated with this key is non-empty and that it contains exactly the amount of entries as each map (the domain)
  requires forall i :: 0 <= i < domain ==> i in women && women[i] != null && women[i].Length == domain // checks the same for women's list
  //ensures forall i :: 0 <= i < domain ==> i in matched && exists j :: 0 <= j < domain && matched[i] == j // ensures that the resulting matching includes all original participants (everyone has a match)
  {
    // need to assert that currentwoman is always in women mapping, might be in matched mapping
    var currentMan: int := 0;
    var freeMen: map := men;
    while (currentMan !in matched)
      decreases forall i :: 0 <= i < domain ==> i !in matched; // amount of free men will decrease
    {
      var preferences: array := men[currentMan]; // get preference list for current man
      var currentWoman: int := 0; // set current woman to top of preference list (so that we immediately go for highest ranking woman on currentMan's list)
      while currentWoman < preferences.Length // while we have not reached the end of the preferences list
        decreases (preferences.Length - currentWoman); // loop termination will occur, because preference list will be iterated through and amount of women to choose from gets smaller
     {
        var highestPrefWoman: int := preferences[currentWoman]; // starting at index 0 of preferences list, highestPreferred woman will be named first
        if (highestPrefWoman !in matched.Values) { // if the highestPreferred woman is not found in the matched mapping
          matched := matched[currentMan := highestPrefWoman]; // add current Man with his highestpreferred woman to mapping
        } else {
          var preferences: array := women[highestPrefWoman];
          var man_matched: int := matched[highestPrefWoman];
          
          // need to find currentwoman's preference list
          // need to find currentwoman's mate on the matched list
          // need to compare index of current woman's match to currentman and see whose higher on the preferences
        }
      }
    }
}