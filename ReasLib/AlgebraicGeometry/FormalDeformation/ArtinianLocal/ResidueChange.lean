module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue

/-!
# Residue-field change for Artinian local algebras
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

/-- The structure map `k → l` is local. -/
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

/-- The second projection of `B ×_l k` is surjective. -/
theorem residueChangeSnd_surjective :
    Function.Surjective (AlgHom.pullbackSnd (toResidue B).hom
      (IsScalarTower.toAlgHom Λ k l)) :=
  sorry

/-- The residue field of `B ×_l k` is identified with `k` by its second projection. -/
noncomputable def residueChangeResidueFieldIso :
    ResidueField (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (IsLocalRing.ker_eq_maximalIdeal
        (AlgHom.pullbackSnd (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)).toRingHom
        (residueChangeSnd_surjective k B)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (residueChangeSnd_surjective k B))

/-- The residue class of a pullback pair maps to its second coordinate. -/
theorem residueChangeResidueFieldIso_residue
    (z : AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) :
    residueChangeResidueFieldIso k B (IsLocalRing.residue _ z) =
      AlgHom.pullbackSnd (toResidue B).hom (IsScalarTower.toAlgHom Λ k l) z :=
  sorry

/-- The fibre product `B ×_l k`, viewed as an object over `k`. -/
noncomputable def residueChange : ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l))
    (residueChangeResidueFieldIso k B)

/-- The bundled residue-change object has the algebra-pullback carrier. -/
theorem residueChange_carrier :
    (residueChange k B).carrier =
      CommRingCat.of (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) :=
  sorry

/-- The first algebra projection `B ×_l k → B`. -/
noncomputable def residueChangeFst : (residueChange k B).carrier →ₐ[Λ] B.carrier :=
  AlgHom.pullbackFst (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)

/-- The second projection is compatible with the chosen residue identifications. -/
theorem residueChangeSnd_residue_compat :
    residueCompat (A := residueChange k B) (B := residue Λ k)
        (AlgHom.pullbackSnd (toResidue B).hom (IsScalarTower.toAlgHom Λ k l))
        (instIsLocalHom_residueChangeSnd k B) = residueIsoHom (residueChange k B) :=
  sorry

/-- The second projection `B ×_l k ⟶ k`. -/
noncomputable def residueChangeSnd : residueChange k B ⟶ residue Λ k :=
  Hom.of (AlgHom.pullbackSnd (toResidue B).hom (IsScalarTower.toAlgHom Λ k l))
    (instIsLocalHom_residueChangeSnd k B) (residueChangeSnd_residue_compat k B)

/-- The underlying algebra map of `residueChangeFst` is the first projection. -/
theorem residueChangeFst_hom :
    residueChangeFst k B =
      AlgHom.pullbackFst (toResidue B).hom (IsScalarTower.toAlgHom Λ k l) :=
  sorry

/-- The underlying algebra map of `residueChangeSnd` is the second projection. -/
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

/-- The explicit product map sends a pullback pair to `(f b, x)`. -/
theorem residueChangeMap_mem {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B')
    (x : AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)) :
    (AlgHom.prodMap f.hom (AlgHom.id Λ k)) x ∈
      AlgHom.pullback (toResidue B').hom (IsScalarTower.toAlgHom Λ k l) :=
  sorry

/-- The algebra map induced by a morphism on residue-change pullbacks. -/
noncomputable def residueChangeMapHom {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B') :
    (residueChange k B).carrier →ₐ[Λ] (residueChange k B').carrier :=
  AlgHom.codRestrict
    ((AlgHom.prodMap f.hom (AlgHom.id Λ k)).comp
      (AlgHom.pullback (toResidue B).hom (IsScalarTower.toAlgHom Λ k l)).val)
    _ (residueChangeMap_mem k f)

/-- The induced algebra map on residue-change pullbacks is local. -/
instance instIsLocalHom_residueChangeMapHom {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B') :
    IsLocalHom (residueChangeMapHom k f) :=
  sorry

/-- The induced algebra map on residue-change pullbacks preserves residue identifications. -/
theorem residueChangeMapHom_residue_compat {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B') :
    residueCompat (residueChangeMapHom k f) (instIsLocalHom_residueChangeMapHom k f) =
      residueIsoHom (residueChange k B) :=
  sorry

/-- The morphism induced by `f` on residue-change pullbacks. -/
noncomputable def residueChangeMap {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B') :
    residueChange k B ⟶ residueChange k B' :=
  Hom.of (residueChangeMapHom k f) (instIsLocalHom_residueChangeMapHom k f)
    (residueChangeMapHom_residue_compat k f)

/-- Residue change sends identity morphisms to identity morphisms. -/
theorem residueChangeMap_id (B : ArtinianLocalAlgCat Λ l) :
    residueChangeMap k (𝟙 B) = 𝟙 (residueChange k B) :=
  sorry

/-- Residue change preserves composition of morphisms. -/
theorem residueChangeMap_comp {B B' B'' : ArtinianLocalAlgCat Λ l}
    (f : B ⟶ B') (g : B' ⟶ B'') :
    residueChangeMap k (f ≫ g) = residueChangeMap k f ≫ residueChangeMap k g :=
  sorry

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
  map_id := residueChangeMap_id k
  map_comp := residueChangeMap_comp k

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
