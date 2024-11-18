-------------------------------------- MODULE Trace --------------------------------------

INSTANCE Integers
INSTANCE FiniteSets
INSTANCE Sequences
INSTANCE ExtendedSequences 
INSTANCE TLC

EmptyTrace == <<>>

Initial(State) == Append(EmptyTrace,State)

vInit(InitialState) == Range(Only(InitialState,"x"))

Next(CurrentTrace,State) == Append(CurrentTrace,State)


==========================================================================================
\* Modification History
\* Last modified Mon Nov 18 11:53:39 BRT 2024 by yuri
\* Created Fri Nov 15 14:48:00 BRT 2024 by yuri
