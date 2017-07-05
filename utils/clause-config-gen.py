for var in [100, 1000, 10000]:
  for clause in [100, 1000, 10000]:
      for neg_prob in [1, 20, 50, 80]:
          for k in [1, 2, 3]:
              filename = 'v' + str(var) + 'c' + str(clause) + 'n' + str(neg_prob) + 'k' + str(k)
              print(str(var) + ' ' + str(clause) + ' ' + str(neg_prob) + ' ' + str(k) + ' ' + filename)