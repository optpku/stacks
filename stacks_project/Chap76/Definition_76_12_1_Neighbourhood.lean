module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap67.Lemma_67_13_3
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_16_3_SchemeTheoreticImage
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap67.Remark_67_12_4_Coborder
public import stacks_project.Chap76.Definition_76_6_5_Conormal
public import stacks_project.Chap76.Definition_76_9_1_FiniteOrder

/-!
# Infinitesimal neighbourhoods of immersions of algebraic spaces

The `n`th infinitesimal neighbourhood of an immersion `i : Z ⟶ X` is the closed
subspace of the coborder open cut out by the `(n + 1)`st power of the coborder
kernel ideal. The canonical maps `Z ⟶ Z_n ⟶ X` realize this as an `n`th-order
thickening of `Z` over `X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Vanishing of a larger quasi-coherent ideal sheaf implies vanishing of any
smaller ideal sheaf. -/
theorem vanishes_of_le {X Y : AlgebraicSpace S} {I J : IdealSubobject X}
    (h : I ≤ J) {f : Y ⟶ X} (hf : vanishes f J) : vanishes f I :=
  sorry

/-- The closed-subspace inclusion induced by an inclusion of quasi-coherent
ideal sheaves. -/
def subschemeInclusion {X : AlgebraicSpace S} {I J : IdealSubobject X}
    [IsQuasiCoherent I] [IsQuasiCoherent J] (h : I ≤ J) :
    subscheme J ⟶ subscheme I where
  app T := TypeCat.ofHom fun (p : (subschemeFunctor J).obj T) ↦
    ⟨p.val, vanishes_of_le h p.property⟩
  naturality := sorry

/-- Nested closed subspaces include into the subspace cut out by the smaller
ideal. -/
theorem subschemeInclusion_subschemeι {X : AlgebraicSpace S}
    {I J : IdealSubobject X} [IsQuasiCoherent I] [IsQuasiCoherent J]
    (h : I ≤ J) : subschemeInclusion h ≫ subschemeι I = subschemeι J :=
  sorry

namespace Hom.InfinitesimalNeighbourhood

variable {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/-- The multiplication map of the `(n + 1)`st tensor power of the coborder
kernel ideal into the structure module of the coborder. -/
def powMul (n : ℕ) :
    Modules.ofComm
      (tensorObj
        (TensorPower.sheaf (commStructureSheaf (coborder i))
          (Modules.toCommSubobject (idealSheafSubobject (IsImmersion.liftCoborder i)))
          (n + 1))
        (Modules.toComm (SheafOfModules.unit (structureSheaf (coborder i))))) ⟶
      SheafOfModules.unit (structureSheaf (coborder i)) :=
  Modules.ofCommMap
      (IdealSheaf.powerAction
        (Modules.toCommSubobject (idealSheafSubobject (IsImmersion.liftCoborder i)))
        (Modules.toComm (SheafOfModules.unit (structureSheaf (coborder i))))
        (n + 1)) ≫
    { val := 𝟙 _ }

/-- `powMul i n` is the recast coborder-kernel power action into `𝒪` of the
coborder. -/
theorem powMul_eq (n : ℕ) :
    powMul i n =
      Modules.ofCommMap
          (IdealSheaf.powerAction
            (Modules.toCommSubobject (idealSheafSubobject (IsImmersion.liftCoborder i)))
            (Modules.toComm (SheafOfModules.unit (structureSheaf (coborder i))))
            (n + 1)) ≫
        { val := 𝟙 _ } :=
  sorry

/-- The quasi-coherent ideal sheaf on the coborder open defining the `n`th
infinitesimal neighbourhood. -/
def ideal (n : ℕ) : IdealSubobject (coborder i) :=
  kernelSubobject (cokernel.π (powMul i n))

/-- The defining ideal of the `n`th infinitesimal neighbourhood is the image of
the coborder-kernel power multiplication map. -/
theorem ideal_eq_kernelSubobject (n : ℕ) :
    ideal i n = kernelSubobject (cokernel.π (powMul i n)) :=
  sorry

/-- The defining ideal of the `n`th infinitesimal neighbourhood is contained in
the coborder kernel ideal. -/
theorem ideal_le_idealSheafSubobject (n : ℕ) :
    ideal i n ≤ idealSheafSubobject (IsImmersion.liftCoborder i) :=
  sorry

/-- The defining ideal of the `n`th infinitesimal neighbourhood is
quasi-coherent. -/
instance instIsQuasiCoherent_ideal (n : ℕ) : IsQuasiCoherent (ideal i n) :=
  sorry

/-- Ordinary section powers of the coborder kernel lie in the sheaf-image
sections of the neighbourhood ideal. -/
theorem sections_pow_le (n : ℕ) (U : (smallEtaleSite (coborder i))ᵒᵖ) :
    IdealSheaf.sections
          (Modules.toCommSubobject (idealSheafSubobject (IsImmersion.liftCoborder i)))
          U ^ (n + 1) ≤
      IdealSheaf.sections (Modules.toCommSubobject (ideal i n)) U :=
  sorry

/-- On affine étale objects, the defining ideal of the `n`th infinitesimal
neighbourhood is the `(n + 1)`st power of the coborder kernel ideal. -/
theorem ideal_apply (n : ℕ) (U : (smallEtaleSite (coborder i))ᵒᵖ)
    [AlgebraicGeometry.IsAffine ((smallEtaleToScheme (coborder i)).obj U.unop)] :
    IdealSheaf.sections (Modules.toCommSubobject (ideal i n)) U =
      IdealSheaf.sections
          (Modules.toCommSubobject (idealSheafSubobject (IsImmersion.liftCoborder i)))
          U ^ (n + 1) :=
  sorry

/-- The `n`th infinitesimal neighbourhood of the source of an immersion, as a
closed subspace of the coborder open. -/
def space (n : ℕ) : AlgebraicSpace S :=
  subscheme (ideal i n)

/-- The infinitesimal-neighbourhood space is the closed subspace cut out by the
corresponding power of the coborder kernel ideal. -/
theorem space_eq_subscheme (n : ℕ) :
    space i n = subscheme (ideal i n) :=
  sorry

/-- The canonical morphism from an infinitesimal neighbourhood to the ambient
algebraic space. -/
def toAmbient (n : ℕ) : space i n ⟶ X :=
  subschemeι (ideal i n) ≫ (IsImmersion.coborderRange i).ι

/-- The canonical morphism from the source of an immersion to its `n`th
infinitesimal neighbourhood. -/
def fromSource (n : ℕ) : Z ⟶ space i n :=
  toIdealImage (IsImmersion.liftCoborder i) ≫
    subschemeInclusion (ideal_le_idealSheafSubobject i n)

/-- The source morphism followed by the closed-subspace inclusion recovers the
coborder closed factor of the immersion. -/
theorem fromSource_subschemeι (n : ℕ) :
    fromSource i n ≫ subschemeι (ideal i n) = IsImmersion.liftCoborder i :=
  sorry

/-- The infinitesimal-neighbourhood factorization recovers the original
immersion. -/
theorem fromSource_toAmbient (n : ℕ) :
    fromSource i n ≫ toAmbient i n = i :=
  sorry

/-- The canonical map from the source to its infinitesimal neighbourhood is a
closed immersion. -/
instance fromSource_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (fromSource i n) :=
  sorry

/-- The canonical map from an infinitesimal neighbourhood to the ambient space
is an immersion. -/
instance toAmbient_isImmersion (n : ℕ) : IsImmersion (toAmbient i n) :=
  sorry

/-- The canonical map from an immersion to its `n`th infinitesimal neighbourhood
is an `n`th-order thickening. -/
instance fromSource_isNthOrderThickening (n : ℕ) :
    IsNthOrderThickening n (fromSource i n) :=
  sorry

/-- The canonical map from an immersion to its first-order infinitesimal
neighbourhood is a first-order thickening. -/
instance fromSource_isFirstOrderThickening :
    IsFirstOrderThickening (fromSource i 1) :=
  sorry

end Hom.InfinitesimalNeighbourhood

end AlgebraicGeometry.AlgebraicSpace
