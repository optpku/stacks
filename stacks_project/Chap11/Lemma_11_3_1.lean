module

public import ReasLib.Algebra.CentralSimple.SimpleModule.DoubleCentralizer
import StacksCheckRecall

@[expose] public section

-- Lemma 11.3.1: Double centralizer theorem for simple rings.
-- The bicommutant of any nonzero right ideal in a simple ring recovers the ring.

@[stacks 0745] #check @IsSimpleRing.bicommutant_bijective
#check @IsSimpleRing.doubleCentralizerRingEquiv

end
