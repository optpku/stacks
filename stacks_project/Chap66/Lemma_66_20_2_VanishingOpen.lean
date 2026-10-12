/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap66.«66_19_6_1_Stalk»

/-!
# Vanishing locus of a local section of an abelian spaces-étale sheaf

A local section of an abelian sheaf on `X_spaces,étale` vanishes on a unique largest
open of `|U|`, compared with open subspaces, étale images, and geometric germs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The inclusion of an open subspace of an étale algebraic space over `X`, postcomposed with
the structure morphism, is étale. -/
theorem etale_openSubspace_comp (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    Etale (W.ι ≫ U.hom) :=
  sorry

/-- The object of `X_spaces,étale` associated to an open subspace of an étale object `U`. -/
def openSubspaceSite (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (W.ι ≫ U.hom) (etale_openSubspace_comp U W)

/-- The structure morphism of `openSubspaceSite U W` is `W.ι ≫ U.hom`. -/
theorem openSubspaceSite_hom (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    (openSubspaceSite U W).hom = W.ι ≫ U.hom :=
  sorry

/-- The underlying algebraic space of `openSubspaceSite U W` is `W`. -/
theorem openSubspaceSite_left (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    (openSubspaceSite U W).left = W.X :=
  sorry

/-- The restriction arrow `W ⟶ U` in `X_spaces,étale` associated to an open subspace of `U`. -/
def openSubspaceHom (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    openSubspaceSite U W ⟶ U :=
  MorphismProperty.Over.homMk W.ι rfl

/-- The underlying morphism of algebraic spaces of `openSubspaceHom U W` is `W.ι`. -/
theorem openSubspaceHom_left (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    (openSubspaceHom U W).left = W.ι :=
  sorry

/-- Restriction of a local section of an abelian sheaf along a morphism of `X_spaces,étale`. -/
def sectionRestrict (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    {U V : spacesEtaleSite X} (φ : V ⟶ U) (σ : F.obj.obj (op U)) : F.obj.obj (op V) :=
  F.obj.map φ.op σ

/-- Restriction of a local section is the underlying presheaf action. -/
theorem sectionRestrict_eq (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    {U V : spacesEtaleSite X} (φ : V ⟶ U) (σ : F.obj.obj (op U)) :
    sectionRestrict F φ σ = F.obj.map φ.op σ :=
  sorry

/-- The largest open of `|U|` on which a local section of an abelian sheaf vanishes, as a
subset of points. -/
def sectionVanishingSet (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) : Set (Points U.left) :=
  {x | ∃ W : OpenSubspace U.left,
      x ∈ W.pointsSet ∧ sectionRestrict F (openSubspaceHom U W) σ = 0}

/-- A point of `|U|` lies in `sectionVanishingSet F U σ` if and only if it lies in some open
subspace of `U` on which `σ` restricts to zero. -/
theorem mem_sectionVanishingSet_iff (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (x : Points U.left) :
    x ∈ sectionVanishingSet F U σ ↔
      ∃ W : OpenSubspace U.left,
        x ∈ W.pointsSet ∧ sectionRestrict F (openSubspaceHom U W) σ = 0 :=
  sorry

/-- The vanishing locus of a local section is open in `|U|`. -/
theorem isOpen_sectionVanishingSet (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) :
    IsOpen (sectionVanishingSet F U σ) :=
  sorry

/-- The vanishing locus of a local section is the point-set of some open subspace of `U`. -/
theorem exists_openSubspace_sectionVanishingSet
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) :
    ∃ W : OpenSubspace U.left, W.pointsSet = sectionVanishingSet F U σ :=
  sorry

/-- The underlying type-valued presheaf of an abelian sheaf on `X_spaces,étale`. -/
def typePresheaf (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1) :=
  F.obj ⋙ forget AddCommGrpCat.{u + 1}

/-- The type-valued presheaf of an abelian sheaf is the forgetful image of its underlying
presheaf. -/
theorem typePresheaf_eq (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    typePresheaf F = F.obj ⋙ forget AddCommGrpCat.{u + 1} :=
  sorry

/-- The étale neighborhood `(U, ū)` of the geometric point `x̄ = (U ⟶ X) ∘ ū`. -/
def neighborhoodOf (U : spacesEtaleSite X) (ubar : GeometricPoint U.left) :
    GeometricPoint.EtaleNeighborhood (ubar.map U.hom) :=
  GeometricPoint.EtaleNeighborhood.of U ubar.hom rfl

/-- The underlying spaces-étale object of `neighborhoodOf U ubar` is `U`. -/
theorem neighborhoodOf_toSpacesEtale (U : spacesEtaleSite X)
    (ubar : GeometricPoint U.left) :
    (neighborhoodOf U ubar).toSpacesEtale = U :=
  sorry

/-- The germ of a local section at a geometric point of `U`, as an element of the spaces-étale
stalk at `x̄ = ubar.map U.hom`. -/
def sectionGerm (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (ubar : GeometricPoint U.left) :
    GeometricPoint.spacesEtaleStalk (ubar.map U.hom) (typePresheaf F) :=
  GeometricPoint.toSpacesEtaleStalk (neighborhoodOf U ubar) σ

/-- The germ of a local section is the spaces-étale colimit inclusion of that section. -/
theorem sectionGerm_eq (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (ubar : GeometricPoint U.left) :
    sectionGerm F U σ ubar =
      GeometricPoint.toSpacesEtaleStalk (neighborhoodOf U ubar) σ :=
  sorry

/-- The zero germ of an abelian sheaf at a geometric point of `U`. -/
def sectionGerm_zero (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (ubar : GeometricPoint U.left) :
    GeometricPoint.spacesEtaleStalk (ubar.map U.hom) (typePresheaf F) :=
  GeometricPoint.toSpacesEtaleStalk (neighborhoodOf U ubar) (0 : F.obj.obj (op U))

/-- The zero germ is the spaces-étale colimit inclusion of the zero section. -/
theorem sectionGerm_zero_eq (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (ubar : GeometricPoint U.left) :
    sectionGerm_zero F U ubar =
      GeometricPoint.toSpacesEtaleStalk (neighborhoodOf U ubar) (0 : F.obj.obj (op U)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
