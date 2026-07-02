needsPackage "CyclicFlats"

H1 = new HashTable from {{} =>0,  {1,2,3,4} => 2}
M1 = cyclicFlats(H1)
print tutte(M1)


H2 = new HashTable from {{} =>0, {3,4} => 1, {1,2,3,4} => 2}
M2 = cyclicFlats(H2)
print tutte(M2)

H3 = new HashTable from {{} =>0,  {1,2,3,4,5} => 2}
M3 = cyclicFlats(H3)
print tutte(M3)

H4 = new HashTable from {{} =>0, {3,4,5} => 1,   {1,2,3,4,5} => 2}
M4 = cyclicFlats(H4)
print tutte(M4)

H5 = new HashTable from {{} =>0, toList(1..14) => 13,  toList(1..28) => 14}
M5 = cyclicFlats(H5)
print tutte(M5)





--H = new HashTable from {{} =>0, {1,2,3} => 2, {4,5,6} => 2, {1,2,3,4,5,6} => 3}

--loadPackage "Matroids"
--U = uniformMatroid(10, 20) --12,24 work but 13, 26 kills the computer 

