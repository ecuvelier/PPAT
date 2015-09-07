# PPAT prototype
Multi-Party Function Evaluation with Perfectly Private Audit Trail
--------------------------------------------------------------------

The modules presented here contain 
- the core arithmetic needed to perform natural operations and pairings on BN- elliptic curves, extension fields, etc.
- instanciations of the CCE primitive
- the NIZKPoK needed to compute the PPAT for the test applications
- the test applications presented in the paper

Running the prototype
---------------------

- the file script.py instantiate the CCE primitive: the PPATS and the PPATC public parameters, public keys and secret keys
- the test modules for the PPAT are respectively test_ppats.py and test_ppatc.py of the ppat package
- to test the applications, load the testApplications.py module of the applications package and then try the functions:
   - testShortestPath(nbClients) --> we recommend < 10 clients
   - testAuctions(nbClients) --> we recommend < 1000 clients
   - testLinearSystem(nbClients) --> we recommend < 4096 clients and square number

Implementing new multi-party protocols
--------------------------------------

Any new multi-party protocol can be implemented -- for example, but not only -- by inheriting the abstract classes of the ppatProtocol.py of the protocols package. Inherit the classes:
- Circuit to design the circuit evaluation (a circuit is composed of the Gate objects)
- Worker
- Client
to compose your multi-party application. See for example the prototype applications presented above.


 
