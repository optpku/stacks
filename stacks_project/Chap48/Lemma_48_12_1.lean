module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.Coproduct
public import stacks_project.Chap48.Lemma_48_3_1_Instances
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.12.1: if `f : X ⟶ Y` is proper, flat, and of finite presentation over a
quasi-compact and quasi-separated scheme, then any right adjoint `a` to derived pushforward
`pushforward f` preserves arbitrary direct sums. -/
@[stacks 0E4I] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjoint_preservesCoproducts_of_proper_flat :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
      [Scheme.Hom.FinitePresentation f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X), (pushforward f ⊣ a) →
      (I : Type u) → PreservesColimitsOfShape (Discrete I) a)

end AlgebraicGeometry.Scheme.DerivedQCoh
