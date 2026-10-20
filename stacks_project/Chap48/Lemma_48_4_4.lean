module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.4.4 -/
@[stacks 0A9P] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.supportOnComplement_boundedBelow_of_proper_of_flat_or_noetherian :
    ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) [IsProper f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (h_finiteness : (Flat f ∧ Scheme.Hom.FinitePresentation f) ∨ IsNoetherian Y)
      (V : Y.Opens) (hV : IsCompact (V : Set Y)) (Q : DerivedQCoh Y)
      (hQ_boundedBelow :
        (t.plus : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)) Q.obj)
      (hQ_support : RingedSpace.ModuleDerived.IsSupportedOn Q.obj (V : Set Y)ᶜ),
      RingedSpace.ModuleDerived.IsSupportedOn
        (a.obj Q).obj (f ⁻¹ᵁ V : Set X)ᶜ)

end AlgebraicGeometry.Scheme.DerivedQCoh
