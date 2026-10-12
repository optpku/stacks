/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/- Lemma 41.14.2: A finite étale morphism whose fibre over `s` is the singleton
`{x}`, with purely inseparable induced extension `κ(s) ⟶ κ(x)`, is an isomorphism
over some open neighbourhood of `s`. -/
@[stacks 04DH]
#check
  (AlgebraicGeometry.Etale.exists_isIso_morphismRestrict :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f]
      (s : S) (x : X) (hxs : f x = s)
      (h_fiber : f ⁻¹' ({s} : Set S) = {x})
      (hκ : ((Scheme.residueFieldCongr hxs).inv ≫
        f.residueFieldMap x).hom.IsPurelyInseparable),
      ∃ U : S.Opens, s ∈ U ∧ IsIso (f ∣_ U))

end AlgebraicGeometry.Etale
