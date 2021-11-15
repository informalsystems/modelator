------------------------- MODULE NumbersTest ----------------------------------
EXTENDS Numbers
-------------------------------------------------------------------------------

AMaxBMaxTest ==
    /\ a = MaxNumber
    /\ b = MaxNumber

AMaxBMinTest ==
    /\ a = MaxNumber
    /\ b = 0

AMinBMaxTest ==
    /\ a = 0
    /\ b = MaxNumber

===============================================================================
