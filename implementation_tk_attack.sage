"""
Implemntation of the TK attack for exposed LSBs.
Reproduces Table 4 and Table 5 of our paper.

Requires Sage 9.3, as it uses LLL transformation matrix.
"""

#Lattice parameters m & t
m = 2
t = 0

print('m = ',m, '& t = ',t)

#n is the size of primes, alpha is the size of e, MSB_size ist the bit-size of the unknown MSBs.
n  =  512
alpha =  16
MSB_size  = 478

#d_p = d_p^(M) * powerOfTwo + d_p^(L), d_q = d_q^(M) * powerOfTwo + d_q^(L)
powerOfTwo = 2^(n-MSB_size)

def keyGen(n,alpha,powerOfTwo):
  """
  Generates a CRT-RSA key pair.

  Args:
    n: bit-size of the primes
    alpha: Size of the public exponent e, i.e., e = N^alpha
    powerOfTwo: The power of 2, at which the MSBs and LSBs of the CRT-exponents get split

  Returns:
    modulus N,
    primes p,q
    public exponent e
    secret exponents d_p,d_q
    parameters k,l
    MSBs of d_p
    LSBs of d_p
    MSBs of d_q
    LSBs of d_q

  """
  while(1):
   p = next_prime(ZZ.random_element(2^(n-1),2^n))
   q = next_prime(ZZ.random_element(2^(n-1),2^n))
   e = ZZ.random_element(2^(alpha-1),2^(alpha))
   N=p*q
   if(N.nbits()==2*n and  (gcd(e, (p-1)*(q-1)) == 1)): #N=pq should be 2n bits
       break
  
  d = e.inverse_mod((p-1)*(q-1))
  dp = d%(p-1)
  dq = d%(q-1)
  k = (e*dp-1)/(p-1)
  
  dp_MSB = dp-dp%powerOfTwo
  dp_MSB = ZZ(dp_MSB/powerOfTwo)
  dp_LSB = dp%powerOfTwo

  dq_MSB = dq-dq%powerOfTwo
  dq_MSB = ZZ(dq_MSB/powerOfTwo)
  dq_LSB = dq%powerOfTwo
   
  e = ZZ(e)
  k = (e*dp-1)/(p-1)
  l = (e*dq-1)/(q-1)
  k = ZZ(k)
  l = ZZ(l)
  
  
  return N,p,q,e,dp,dq,k,l, dp_MSB, dp_LSB, dq_MSB, dq_LSB






N,p,q,e,dp,dq,k,l, dp_MSB, dp_LSB, dq_MSB, dq_LSB  = keyGen(n,alpha,powerOfTwo)

# X, Y, Z and W corresponds to the upper bound of dp_MSB, dq_MSB, k and l respectively 
X = 2^MSB_size
Y = 2^MSB_size
Z = 2^alpha
W = 2^alpha


R.<x1,x2,y1,y2> = QQ[]
f_dLSBs = (e*(powerOfTwo*x1+dp_LSB)-1+y1)*(e*(powerOfTwo*x2+dq_LSB)-1+y2)-y1*y2*N 

#Remove common factor from each coefficients of g to make g irreducible.
FACT = factor(f_dLSBs)
f_dLSBs = FACT[0][0]



#S will contain monomials of (f_dLSBs)^m together with extra shifts
S = []
for i_y1 in range(m+1+t):
  for i_y2 in range(m+1+t):
   for i_x1 in range(m+t-i_y1+1):
      for i_x2 in range(m+t-i_y2+1):
         S.append(x1^i_x1*x2^i_x2*y1^i_y1*y2^i_y2)
         



MON = [] #MON will contain monomials of (f_dLSBs)^{m+1} together with extra shifts
F = [] #F will contain shift polynomials
S1 = [] # Since e is small, absolute value of maximal coefficient of f_dLSBs is N-1, which is the coefficient of y1*y2. S1 contains monomials x1^i1*x2^i2*y1^(i3+1)*y2^(i4+1) 
        # where x1^i1*x2^i2*y1^i3*y2^i4 is in S  
for i in range(len(S)):
   MON = union(MON,(S[i]*f_dLSBs).monomials())
   F.append(S[i]*f_dLSBs)
   S1.append(S[i]*y1*y2)
   
 

MS = Set(MON).difference(Set(S1)) #MS contains monomials which correspond to the initial rows. This set will be used to rearrange the monomials in M.

M = [] #Initial monomials of M are from MS. Later monomials are from S1
for i in range(len(MS)):
  M.append(MS[i])

for i in range(len(S1)):
  M.append(S1[i])



a = len(M)
b = len(S1)

M1 = zero_matrix(QQ, a, a-b) #M1 corresponds left side of Coppersmith matrix. 
M2 = zero_matrix(ZZ, a, b)     #M2 corresponds right side of Coppersmith matrix. 


#Upper (a-b,a-b) block of M1 is diagonal where the rows represent the monomials from MS. Last b many rows of M1 are zero only.
for i in range(a-b): 
    M1[i,i] = 1/M[i](X,Y,Z,W)



#M2 represent the shift polynomials from F. 
for i in range(b):
  f = F[i]
  for j in range(a):
     cij = f.coefficient(M[j])
     cij = cij(0,0,0,0)
     M2[j,i] = cij

"""

Perform unimodular transformation over M2 so that last b many rows are unit vectors. These rows contain either 1 or -1 only in one coordinate. All other coordinates are zero. 
Since LLL is a unimodular transformation, we apply LLL over M2. H1 is the corresponding transformation matrix. 

"""
R, H1  = M2.LLL(transformation = True) # 


#Apply unimodular transformation matrix H1 on M1
M_tilda = H1*M1

#M_cap contains initial a-b many rows of M_tilda
M_cap = zero_matrix(QQ,a-b)
for i in range(a-b):
    for j in range(a-b):
        M_cap[i,j] = M_tilda[i,j]
 
print('Lattice Dimension', a-b)

from time import process_time
TIME_Start = process_time()
#Apply LLL operation over M_cap
B2 = M_cap.LLL()
TIME_Stop = process_time()
print('LLL time', TIME_Stop-TIME_Start)

 
#H2 is the transformation matrix of LLL algorithm when it is applied on M_cap
H2 = B2*M_cap^(-1)

v = vector(M)*H1^(-1)

#Vector v_sh shortened vector v to its first a-b entries
v_sh = []
for i in range(a-b):
    v_sh.append(v[i])
v_sh = vector(v_sh)  

v_sh_prime = vector(v_sh)*H2^(-1)

#F contains all polynomial whose root is (dp_MSB,dq_MSB,k,l)
F = [f_dLSBs]
i = a-b-1
while(i>= 0):
    f = v_sh_prime[i]
    if(f(dp_MSB,dq_MSB,k,l) == 0):
        F.append(f)
        
    else:
        break
    i = i-1    

"""
Since all components of the root are less than p, we consider the polynomials of F as modular polynomials over GF(p). Then 
try to find the root using Groebner basis. So we first define a polynomial ring with 4 variables with modulo p.
""" 

MOD = PolynomialRing(GF(p), 4, 'X')
NEW_F = []
for i in range(len(F)):
      NEW_F.append(MOD(F[i]))


set_verbose(-1)
I = (NEW_F)*MOD

B = I.groebner_basis()


print(" ")
print('Grobner basis: ',  B)
print(" ")

for i in range(len(B)):
   print('Estimated values: ', p-B[i](0,0,0,0))

print(" ")

print('dp_MSB = ', dp_MSB)
print('dq_MSB = ',dq_MSB)
print('k = ',k)
print('l = ',l)



