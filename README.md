# paillier

a haskell implementation of [SecureScala](http://www.guidosalvaneschi.com/attachments/papers/2016_SecureScala-Scala-Embedding-of-Secure-Computations_pdf.pdf)

## theory

we have 


Scheme   | Operation | Input type | Scheme type
---------|-----------|------------|------------
Paillier | Addition | Integers | Asymmetric | 
ElGamal  | Multiplication | Integers | Symmetric |
AES      | Equality | Integers, Strings | Asymmetric |
OPE      | Ord      | Integers, Strings | Symmetric |
