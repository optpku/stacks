/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp.Functor
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Mayer--Vietoris cohomology for ringed spaces

This leaf owns the ringed-space view of the site-theoretic Mayer--Vietoris sequence.  The
underlying additive sheaf is the canonical forgetful view of an `𝒪_X`-module; the union
identification is recorded by an explicit cohomology isomorphism rather than by a local
instance or a hidden rewrite.  The sequence map and its functoriality are separate owners so
later arguments can use only the part of the API they need.
-/

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The underlying additive sheaf of a module on `X`. -/
abbrev underlying (F : X.Modules) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf X).obj F

/-- The Mayer--Vietoris square of two opens of `X`. -/
@[stacks 01EB "Mayer--Vietoris square of two opens"]
noncomputable abbrev square (U V : Opens X.carrier) :
    (Opens.grothendieckTopology X).MayerVietorisSquare :=
  Opens.mayerVietorisSquare U V

/-- The cohomology isomorphism induced by a cover equation `U ⊔ V = ⊤`. -/
@[stacks 01EB "cohomology transport along the union identification"]
noncomputable abbrev unionIso (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) (n : ℕ) :
    (underlying F).H' n (U ⊔ V) ≅ (underlying F).H' n ⊤ :=
  (underlying F).cohomologyPresheaf n |>.mapIso (eqToIso hUV).symm.op

/-- The five-arrow Mayer--Vietoris segment for a cover of `X` by `U` and `V`, with the union
term transported to the global cohomology term. -/
@[stacks 01EB "Mayer--Vietoris sequence for module cohomology"]
noncomputable def sequence (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) (n : ℕ) : ComposableArrows AddCommGrpCat.{u} 5 :=
  ComposableArrows.mk₅
    ((unionIso U V hUV F n).inv ≫
      (Opens.mayerVietorisSquare U V).toBiprod (underlying F) n)
    ((Opens.mayerVietorisSquare U V).fromBiprod (underlying F) n)
    ((Opens.mayerVietorisSquare U V).δ (underlying F) n (n + 1) rfl ≫
      (unionIso U V hUV F (n + 1)).hom)
    ((unionIso U V hUV F (n + 1)).inv ≫
      (Opens.mayerVietorisSquare U V).toBiprod (underlying F) (n + 1))
    ((Opens.mayerVietorisSquare U V).fromBiprod (underlying F) (n + 1))

/-- Exactness of the five-arrow Mayer--Vietoris segment. -/
@[stacks 01EB "exactness of the Mayer--Vietoris segment"]
theorem sequence_exact (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) (n : ℕ) :
    (sequence U V hUV F n).Exact := sorry

/-- The cohomology map on an open induced by a morphism of modules. -/
@[stacks 01EB "cohomology map on an open"]
noncomputable abbrev mapAt {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (W : Opens X.carrier) :
    (underlying F).H' n W ⟶ (underlying G).H' n W :=
  CategoryTheory.Sheaf.cohomologyMap ((moduleUnderlyingSheaf X).map φ) n W

/-- The map on the two-open biproduct induced by a module morphism. -/
@[stacks 01EB "biproduct cohomology map on two opens"]
noncomputable abbrev mapBiprod {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (U V : Opens X.carrier) :
    (underlying F).H' n U ⊞ (underlying F).H' n V ⟶
      (underlying G).H' n U ⊞ (underlying G).H' n V :=
  biprod.map (mapAt φ n U) (mapAt φ n V)

/-- Naturality of the first arrow in the Mayer--Vietoris segment. -/
theorem map_naturality_zero {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (sequence U V hUV F n).map' 0 1 ≫ mapBiprod φ n U V =
      mapAt φ n ⊤ ≫ (sequence U V hUV G n).map' 0 1 := sorry

/-- Naturality of the second arrow in the Mayer--Vietoris segment. -/
theorem map_naturality_one {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (sequence U V hUV F n).map' 1 2 ≫ mapAt φ n (U ⊓ V) =
      mapBiprod φ n U V ≫ (sequence U V hUV G n).map' 1 2 := sorry

/-- Naturality of the connecting arrow in the Mayer--Vietoris segment. -/
theorem map_naturality_two {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (sequence U V hUV F n).map' 2 3 ≫ mapAt φ (n + 1) ⊤ =
      mapAt φ n (U ⊓ V) ≫ (sequence U V hUV G n).map' 2 3 := sorry

/-- Naturality of the fourth arrow in the Mayer--Vietoris segment. -/
theorem map_naturality_three {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (sequence U V hUV F n).map' 3 4 ≫ mapBiprod φ (n + 1) U V =
      mapAt φ (n + 1) ⊤ ≫ (sequence U V hUV G n).map' 3 4 := sorry

/-- Naturality of the fifth arrow in the Mayer--Vietoris segment. -/
theorem map_naturality_four {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (sequence U V hUV F n).map' 4 5 ≫ mapAt φ (n + 1) (U ⊓ V) =
      mapBiprod φ (n + 1) U V ≫ (sequence U V hUV G n).map' 4 5 := sorry

/-- The morphism of Mayer--Vietoris segments induced by a module morphism. -/
@[stacks 01EB "morphism of Mayer--Vietoris segments"]
noncomputable def sequenceMap {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    sequence U V hUV F n ⟶ sequence U V hUV G n :=
  homMk₅ (mapAt φ n ⊤) (mapBiprod φ n U V) (mapAt φ n (U ⊓ V))
    (mapAt φ (n + 1) ⊤) (mapBiprod φ (n + 1) U V)
    (mapAt φ (n + 1) (U ⊓ V))
    (map_naturality_zero φ U V hUV n)
    (map_naturality_one φ U V hUV n)
    (map_naturality_two φ U V hUV n)
    (map_naturality_three φ U V hUV n)
    (map_naturality_four φ U V hUV n)

/-- The segment map induced by an identity morphism is the identity. -/
@[stacks 01EB "identity law for Mayer--Vietoris segment maps"]
theorem sequenceMap_id (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) (n : ℕ) :
    sequenceMap (𝟙 F) U V hUV n = 𝟙 _ := sorry

/-- Segment maps respect composition of module morphisms. -/
@[stacks 01EB "composition law for Mayer--Vietoris segment maps"]
theorem sequenceMap_comp (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (n : ℕ) :
    sequenceMap (φ ≫ ψ) U V hUV n =
      sequenceMap φ U V hUV n ≫ sequenceMap ψ U V hUV n := sorry

/-- The Mayer--Vietoris segment as a functor of the coefficient module. -/
@[stacks 01EB "functorial Mayer--Vietoris segment"]
noncomputable def functor (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    X.Modules ⥤ ComposableArrows AddCommGrpCat.{u} 5 where
  obj F := sequence U V hUV F n
  map φ := sequenceMap φ U V hUV n
  map_id F := sequenceMap_id U V hUV F n
  map_comp φ ψ := sequenceMap_comp U V hUV φ ψ n

/-- Prefix the degree-zero Mayer--Vietoris segment by the zero morphism. -/
@[stacks 01EB "augmented Mayer--Vietoris segment"]
noncomputable abbrev augmented (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) : ComposableArrows AddCommGrpCat.{u} 6 :=
  (sequence U V hUV F 0).zeroPrecomp 1

/-- Exactness of the degree-zero augmented Mayer--Vietoris segment beginning with `0`. -/
@[stacks 01EB "exactness of the augmented Mayer--Vietoris segment"]
theorem augmented_exact (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) :
    (augmented U V hUV F).Exact := sorry

/-- The degree-zero augmented Mayer--Vietoris segment as a functor of the coefficient module. -/
@[stacks 01EB "functorial augmented Mayer--Vietoris segment"]
noncomputable abbrev augmentedFunctor (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    : X.Modules ⥤ ComposableArrows AddCommGrpCat.{u} 6 :=
  functor U V hUV 0 ⋙ ComposableArrows.zeroPrecomp.functor 1

end AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris
