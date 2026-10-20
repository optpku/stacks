module

public import ReasLib.RingTheory.Projective.FiniteDual
import StacksCheckRecall

@[expose] public section

/- Remark 110.34.3. The prefix-ones ideal is a non-finitely generated projective module
whose dual is isomorphic to the product ring and is finite free. -/
@[stacks 0H8D] #check (PrefixOnes.dualEquiv :
  Module.Dual (ℕ → ZMod 2) PrefixOnes.ideal ≃ₗ[ℕ → ZMod 2] (ℕ → ZMod 2))

#check (PrefixOnes.not_finite : ¬ Module.Finite (ℕ → ZMod 2) PrefixOnes.ideal)
#check (PrefixOnes.instProjective : Module.Projective (ℕ → ZMod 2) PrefixOnes.ideal)
#check (PrefixOnes.instFinite_dual :
  Module.Finite (ℕ → ZMod 2) (Module.Dual (ℕ → ZMod 2) PrefixOnes.ideal))
#check (PrefixOnes.instFree_dual :
  Module.Free (ℕ → ZMod 2) (Module.Dual (ℕ → ZMod 2) PrefixOnes.ideal))
