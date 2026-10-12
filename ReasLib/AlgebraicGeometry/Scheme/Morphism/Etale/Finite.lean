/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.OpenImmersion

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Etale

/-- A finite étale morphism with a singleton fibre and purely inseparable residue-field
extension restricts to an isomorphism over an open neighbourhood of the image point. -/
theorem exists_isIso_morphismRestrict
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f]
    (s : S) (x : X) (hxs : f x = s)
    (h_fiber : f ⁻¹' ({s} : Set S) = {x})
    (hκ : ((Scheme.residueFieldCongr hxs).inv ≫
      f.residueFieldMap x).hom.IsPurelyInseparable) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso (f ∣_ U) := sorry

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite étale morphism admits, étale-locally around any point of the target, a finite
pairwise disjoint clopen decomposition whose pieces map isomorphically to the neighbourhood. -/
theorem exists_clopen_decomposition_isIso_of_finite
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f] (s : S) :
    ∃ (U : EtaleNeighborhood S s) (n : ℕ),
      let P := pullback f U.toEtale.hom
      let p := pullback.snd f U.toEtale.hom
      ∃ (V : Fin n → P.Opens)
        (_ : iSup V = ⊤)
        (_ : Pairwise (fun i j ↦ Disjoint (V i : Set P) (V j : Set P)))
        (_ : ∀ i, IsClopen (V i : Set P)),
        ∀ i, IsIso ((V i).ι ≫ p) := sorry

end AlgebraicGeometry.Scheme.Hom
