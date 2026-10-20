module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Unramified

/- Lemma 41.7.3: A finite unramified morphism whose fibre over `s` is the singleton
`{x}`, with purely inseparable induced extension `κ(s) ⟶ κ(x)`, restricts to a closed
immersion over some open neighbourhood of `s`. -/
@[stacks 04DG] #check
  (AlgebraicGeometry.Unramified.exists_isClosedImmersion_morphismRestrict :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Unramified f]
      (s : S) (x : X) (hxs : f x = s)
      (h_fiber : f ⁻¹' ({s} : Set S) = {x})
      (hκ : ((Scheme.residueFieldCongr hxs).inv ≫
        f.residueFieldMap x).hom.IsPurelyInseparable),
      ∃ U : S.Opens, s ∈ U ∧ IsClosedImmersion (f ∣_ U))

end AlgebraicGeometry.Unramified
