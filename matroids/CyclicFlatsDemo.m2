needsPackage "CyclicFlats"

--H = new HashTable from {{} =>0, {3,4} => 1, {1,2,3,4} => 2}

--H = new HashTable from {{} =>0, {1,2,3} => 2, {4,5,6} => 2, {1,2,3,4,5,6} => 3}

--cyclicFlats H
  
loadPackage "Matroids"
--U = uniformMatroid(10, 20) --12,24 work but 13, 26 kills the computer 
print 1..20

