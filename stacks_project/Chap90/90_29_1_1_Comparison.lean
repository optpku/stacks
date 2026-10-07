module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.RingTheory.LocalRing.Pullback
public import stacks_project.Chap90.Lemma_90_10_7_DualNumber

/-!
# Residue-field change for `ArtinianLocalAlgCat`

A finite field extension `k → l` induces a comparison functor
`ArtinianLocalAlgCat Λ l ⥤ ArtinianLocalAlgCat Λ k` sending `B` to the
algebra fibre product of `toResidue B` along `k → l`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace ArtinianLocalAlgCat

section ResidueChange

variable {Λ l : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field l] [Algebra Λ l]
  [Module.Finite Λ l]
variable (k : Type u) [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable (B : ArtinianLocalAlgCat Λ l)

/-- The structure map `k → l` is local, as a map out of a field. -/
instance instIsLocalHom_toAlgHom :
    IsLocalHom (IsScalarTower.toAlgHom Λ k l) :=
  sorry

/-- The fibre product `B ×_l k` is a local ring. -/
instance instIsLocalRing_residueChange :
    IsLocalRing (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) :=
  AlgHom.isLocalRing_pullback _ _

/-- The fibre product `B ×_l k` is Artinian. -/
instance instIsArtinianRing_residueChange :
    IsArtinianRing (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) :=
  sorry

/-- The first algebra projection of `B ×_l k` is local. -/
instance instIsLocalHom_residueChangeFst :
    IsLocalHom (AlgHom.pullbackFst (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) :=
  sorry

/-- The second algebra projection of `B ×_l k` is local. -/
instance instIsLocalHom_residueChangeSnd :
    IsLocalHom (AlgHom.pullbackSnd (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) :=
  sorry

/-- Forward residue identification of `B ×_l k` with `k`, via the second projection
and the residue identification of `k`. -/
noncomputable def residueChangeResidueFieldIsoHom :
    ResidueField (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) →ₐ[Λ] k where
  toFun := fun z ↦
    (residue Λ k).residueFieldIso
      (Ideal.Quotient.mk _
        (AlgHom.pullbackSnd (toResidue B).hom (IsScalarTower.toAlgHom Λ k l) (Quotient.out z)))
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Inverse residue identification of `B ×_l k`, sending `x : k` to the residue class of
the pair `(surjInv (toResidue B) (algebraMap k l x), x)`. -/
noncomputable def residueChangeResidueFieldIsoInv :
    k →ₐ[Λ]
      ResidueField (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) where
  toFun := fun x ↦
    Ideal.Quotient.mk _
      ⟨(Function.surjInv
          (B.residueFieldIso.surjective.comp
            (Ideal.Quotient.mkₐ_surjective Λ (maximalIdeal B.carrier)))
          (algebraMap k l x),
        x),
        sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Residue-field identification of `B ×_l k` with `k`, via the second projection. -/
noncomputable def residueChangeResidueFieldIso :
    ResidueField (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom (residueChangeResidueFieldIsoHom k B)
    (residueChangeResidueFieldIsoInv k B) sorry sorry

/-- The fibre product `B ×_l k`, viewed as an object of `ArtinianLocalAlgCat Λ k`. -/
noncomputable def residueChange : ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l))
    (residueChangeResidueFieldIso k B)

/-- The bundled residue-change object has the algebra-pullback carrier. -/
theorem residueChange_carrier :
    (residueChange k B).carrier =
      AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l) :=
  sorry

/-- The first algebra projection `B ×_l k → B`. -/
noncomputable def residueChangeFst : (residueChange k B).carrier →ₐ[Λ] B.carrier :=
  AlgHom.pullbackFst (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)

/-- The second projection `B ×_l k ⟶ k` in `ArtinianLocalAlgCat Λ k`. -/
noncomputable def residueChangeSnd : residueChange k B ⟶ residue Λ k where
  hom := AlgHom.pullbackSnd (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `residueChangeFst` is the first algebra projection. -/
theorem residueChangeFst_hom :
    residueChangeFst k B =
      AlgHom.pullbackFst (toResidue B).hom (IsScalarTower.toAlgHom Λ k l) :=
  sorry

/-- The underlying algebra map of `residueChangeSnd` is the second algebra projection. -/
theorem residueChangeSnd_hom :
    (residueChangeSnd k B).hom =
      AlgHom.pullbackSnd (toResidue B).hom (IsScalarTower.toAlgHom Λ k l) :=
  sorry

end ResidueChange

section ResidueChangeMap

variable {Λ l : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field l] [Algebra Λ l]
  [Module.Finite Λ l]
variable (k : Type u) [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]

/-- Action of residue change on morphisms, by `f × id` on the pullback. -/
noncomputable def residueChangeMap {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B') :
    residueChange k B ⟶ residueChange k B' where
  hom :=
    AlgHom.codRestrict
      ((AlgHom.prodMap f.hom (AlgHom.id Λ k)).comp
        (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)).val)
      (AlgHom.pullback (toResidue B').hom (IsScalarTower.toAlgHom Λ k l)) sorry
  isLocalHom := sorry
  residue_compat := sorry

end ResidueChangeMap

section ResidueChangeFunctor

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]

/-- The comparison functor `C_{Λ, l} ⥤ C_{Λ, k}` sending `B` to `B ×_l k`. -/
noncomputable def residueChangeFunctor :
    ArtinianLocalAlgCat Λ l ⥤ ArtinianLocalAlgCat Λ k where
  obj := residueChange k
  map := residueChangeMap k
  map_id := sorry
  map_comp := sorry

/-- The object map of `residueChangeFunctor` is `residueChange`. -/
theorem residueChangeFunctor_obj (B : ArtinianLocalAlgCat Λ l) :
    (residueChangeFunctor Λ k l).obj B = residueChange k B :=
  sorry

/-- The morphism map of `residueChangeFunctor` is `residueChangeMap`. -/
theorem residueChangeFunctor_map {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B') :
    (residueChangeFunctor Λ k l).map f = residueChangeMap k f :=
  sorry

end ResidueChangeFunctor

end ArtinianLocalAlgCat
