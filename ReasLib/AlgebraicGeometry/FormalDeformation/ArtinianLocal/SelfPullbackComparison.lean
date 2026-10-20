module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SelfPullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Kernel
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroPullback

/-!
# Comparison isomorphism `A' ×_A A' ≅ A' ×_k k[I]`

For a surjection `f : A' ⟶ A` whose kernel `I` is annihilated by `m_{A'}`, the map
`g(a1, a2) = residue(a1) ⊕ (a2 - a1)` induces an isomorphism of objects of `C_Λ`
sending `(a1, a2)` to `(a1, g(a1, a2))` and commuting with first projections to `A'`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A A' : ArtinianLocalAlgCat Λ k}

/-- The difference `a2 - a1` of a pair in `A' ×_A A'` as an element of `kerModule f`. -/
noncomputable def selfPullbackKerDiff (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (z : (selfPullback f).carrier) : kerModule f hI :=
  ⟨AlgHom.pullbackSnd f.hom f.hom z - AlgHom.pullbackFst f.hom f.hom z, sorry⟩

/-- The map `g : A' ×_A A' ⟶ k[I]` given by `g(a1, a2) = residue(a1) ⊕ (a2 - a1)`. -/
noncomputable def selfPullbackDiff (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) :
    selfPullback f ⟶ squareZero Λ k (kerModule f hI) :=
  Hom.of
    { toFun := fun z =>
        (inl ((toResidue A').hom (AlgHom.pullbackFst f.hom f.hom z)) :
            TrivSqZeroExt k (kerModule f hI)) +
          inr (selfPullbackKerDiff f hI z)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
    sorry sorry

/-- `selfPullbackDiff` evaluates to `inl (toResidue a1) + inr (a2 - a1)`. -/
theorem selfPullbackDiff_apply (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (z : (selfPullback f).carrier) :
    (selfPullbackDiff f hI).hom z =
      (inl ((toResidue A').hom (AlgHom.pullbackFst f.hom f.hom z)) :
          TrivSqZeroExt k (kerModule f hI)) +
        inr (selfPullbackKerDiff f hI z) := sorry

/-- The underlying algebra map of the comparison `(a1, a2) ↦ (a1, g(a1, a2))`. -/
noncomputable def selfPullbackIsoHom (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) :
    selfPullback f ⟶ squareZeroPullback A' (kerModule f hI) :=
  Hom.of
    (AlgHom.codRestrict
      (AlgHom.prod (selfPullbackFst f).hom (selfPullbackDiff f hI).hom)
      (AlgHom.pullback (toResidue A').hom (squareZeroToResidue Λ k (kerModule f hI)).hom)
      sorry)
    sorry sorry

/-- The inverse comparison `(a, residue ⊕ i) ↦ (a, a + i)`. -/
noncomputable def selfPullbackIsoInv (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) :
    squareZeroPullback A' (kerModule f hI) ⟶ selfPullback f :=
  Hom.of
    { toFun := fun z =>
        let a :=
          AlgHom.pullbackFst (toResidue A').hom
            (squareZeroToResidue Λ k (kerModule f hI)).hom z
        let t :=
          AlgHom.pullbackSnd (toResidue A').hom
            (squareZeroToResidue Λ k (kerModule f hI)).hom z
        ⟨(a, a + t.snd.1), sorry⟩
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
    sorry sorry

/-- The isomorphism `A' ×_A A' ≅ A' ×_k k[I]` given by `(a1, a2) ↦ (a1, g(a1, a2))`. -/
noncomputable def selfPullbackIso (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) :
    selfPullback f ≅ squareZeroPullback A' (kerModule f hI) where
  hom := selfPullbackIsoHom f hI
  inv := selfPullbackIsoInv f hI
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The comparison isomorphism commutes with first projections to `A'`. -/
theorem selfPullbackIso_hom_fst (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) :
    (selfPullbackIso f hI).hom ≫ squareZeroPullbackFst A' (kerModule f hI) =
      selfPullbackFst f := sorry

/-- The comparison isomorphism commutes with the structure maps to `A`. -/
theorem selfPullbackIso_comp_toA (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) :
    (selfPullbackIso f hI).hom ≫ squareZeroPullbackToBase A' (kerModule f hI) f =
      selfPullbackToBase f := sorry

end ArtinianLocalAlgCat
