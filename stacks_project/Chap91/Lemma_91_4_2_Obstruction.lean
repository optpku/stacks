module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import stacks_project.Chap91.«91_4_0_1_Extension»
public import stacks_project.Chap91.Remark_91_4_7_Extension
public import stacks_project.Chap91.Lemma_91_4_1_Compatible

/-!
# Obstruction class of a map of mixed-scalar extensions

Along a first-order thickening, a pair of mixed-scalar module extensions together with maps of
the endpoint `𝒪_X`-modules whose infinitesimal-map square commutes determines a canonical class
in `Ext ℱ ℒ 1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace (Modules)
open CategoryTheory.Abelian (Ext)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ModuleExtension

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'}

/-- A morphism of mixed-scalar module extensions along `i`, given by maps of the kernel,
middle, and cokernel modules making both short-exact squares commute. -/
structure Hom (E G : ModuleExtension i) where
  /-- The map `ψ : 𝒦 ⟶ ℒ` of kernel `𝒪_X`-modules. -/
  kernel : E.kernel ⟶ G.kernel
  /-- The map `φ : ℱ ⟶ 𝒢` of cokernel `𝒪_X`-modules. -/
  cokernel : E.cokernel ⟶ G.cokernel
  /-- The map `φ' : ℱ' ⟶ 𝒢'` of middle `𝒪_{X'}`-modules. -/
  middle : E.middle ⟶ G.middle
  /-- Compatibility of `φ'` with the inclusions of `i _* 𝒦` and `i _* ℒ`. -/
  comm_ι : E.ι ≫ middle = (i _*).map kernel ≫ G.ι
  /-- Compatibility of `φ'` with the projections onto `i _* ℱ` and `i _* 𝒢`. -/
  comm_π : middle ≫ G.π = E.π ≫ (i _*).map cokernel

namespace Hom

/-- Assemble a morphism of mixed-scalar extensions from endpoint maps, a middle map, and the
two commuting squares. -/
noncomputable def ofMaps {E G : ModuleExtension i}
    (ψ : E.kernel ⟶ G.kernel) (φ : E.cokernel ⟶ G.cokernel)
    (φ' : E.middle ⟶ G.middle)
    (hι : E.ι ≫ φ' = (i _*).map ψ ≫ G.ι)
    (hπ : φ' ≫ G.π = E.π ≫ (i _*).map φ) : Hom E G where
  kernel := ψ
  cokernel := φ
  middle := φ'
  comm_ι := hι
  comm_π := hπ

/-- The identity morphism of a mixed-scalar module extension. -/
noncomputable def id (E : ModuleExtension i) : Hom E E where
  kernel := 𝟙 E.kernel
  cokernel := 𝟙 E.cokernel
  middle := 𝟙 E.middle
  comm_ι := sorry
  comm_π := sorry

/-- Composition of morphisms of mixed-scalar module extensions. -/
noncomputable def comp {E₁ E₂ E₃ : ModuleExtension i}
    (α : Hom E₁ E₂) (β : Hom E₂ E₃) : Hom E₁ E₃ where
  kernel := α.kernel ≫ β.kernel
  cokernel := α.cokernel ≫ β.cokernel
  middle := α.middle ≫ β.middle
  comm_ι := sorry
  comm_π := sorry

/-- A morphism of mixed-scalar extensions is determined by commuting with both the kernel
inclusions and the cokernel projections. -/
theorem spec {E G : ModuleExtension i} (h : Hom E G) :
    E.ι ≫ h.middle = (i _*).map h.kernel ≫ G.ι ∧
      h.middle ≫ G.π = E.π ≫ (i _*).map h.cokernel := sorry

/-- The underlying morphism of short complexes of `𝒪_{X'}`-modules. -/
noncomputable def toShortComplex {E G : ModuleExtension i} (h : Hom E G) :
    E.toShortComplex ⟶ G.toShortComplex where
  τ₁ := (i _*).map h.kernel
  τ₂ := h.middle
  τ₃ := (i _*).map h.cokernel
  comm₁₂ := sorry
  comm₂₃ := sorry

end Hom

variable [IsFirstOrderThickening i]

/-- The infinitesimal-map square of `φ : ℱ ⟶ 𝒢` and `ψ : 𝒦 ⟶ ℒ` commutes. -/
def infinitesimalMap_comm (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) : Prop :=
  CommSq E.infinitesimalMap_restrict (tensorHom (𝟙 (idealModule i)) φ) ψ
    G.infinitesimalMap_restrict

/-- Commutativity of the infinitesimal-map square is equality of the two `𝒪_X`-linear composites
`ℐ ⊗ ℱ ⟶ ℒ`. -/
theorem infinitesimalMap_comm_iff (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    infinitesimalMap_comm E G φ ψ ↔
      E.infinitesimalMap_restrict ≫ ψ =
        tensorHom (𝟙 (idealModule i)) φ ≫ G.infinitesimalMap_restrict := sorry

/-- Pushout of a mixed-scalar extension along a map of kernel `𝒪_X`-modules. -/
noncomputable def pushoutExtension (E : ModuleExtension i) {K : X.Modules}
    (ψ : E.kernel ⟶ K) :
    CategoryTheory.Extension ((i _*).obj K) ((i _*).obj E.cokernel) :=
  CategoryTheory.Extension.pushout ((i _*).map ψ) E.toExtension

/-- `pushoutExtension` is `Extension.pushout` of `toExtension` along `i _* ψ`. -/
theorem pushoutExtension_eq (E : ModuleExtension i) {K : X.Modules}
    (ψ : E.kernel ⟶ K) :
    pushoutExtension E ψ =
      CategoryTheory.Extension.pushout ((i _*).map ψ) E.toExtension := sorry

/-- Pullback of a mixed-scalar extension along a map of cokernel `𝒪_X`-modules. -/
noncomputable def pullbackExtension (G : ModuleExtension i) {F : X.Modules}
    (φ : F ⟶ G.cokernel) :
    CategoryTheory.Extension ((i _*).obj G.kernel) ((i _*).obj F) :=
  CategoryTheory.Extension.pullback ((i _*).map φ) G.toExtension

/-- `pullbackExtension` is `Extension.pullback` of `toExtension` along `i _* φ`. -/
theorem pullbackExtension_eq (G : ModuleExtension i) {F : X.Modules}
    (φ : F ⟶ G.cokernel) :
    pullbackExtension G φ =
      CategoryTheory.Extension.pullback ((i _*).map φ) G.toExtension := sorry

/-- The difference, in `X'.Modules`, of the pushout of `E` along `ψ` and the pullback of `G`
along `φ`. -/
noncomputable def differenceExtension (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    CategoryTheory.Extension ((i _*).obj G.kernel) ((i _*).obj E.cokernel) :=
  CategoryTheory.Extension.baerSum (pushoutExtension E ψ)
    (CategoryTheory.Extension.neg (pullbackExtension G φ))

/-- `differenceExtension` is the Baer difference of `pushoutExtension` and `pullbackExtension`. -/
theorem differenceExtension_eq (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    differenceExtension E G φ ψ =
      CategoryTheory.Extension.baerSum (pushoutExtension E ψ)
        (CategoryTheory.Extension.neg (pullbackExtension G φ)) := sorry

/-- The source complex `𝒦 ⟶ ℱ' ⊞ 𝒢' ⟶ 𝒢` whose middle homology represents the obstruction. -/
noncomputable def differenceShortComplex (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    ShortComplex X'.Modules :=
  ShortComplex.mk (biprod.lift E.ι (-((i _*).map ψ ≫ G.ι)))
    (biprod.desc (E.π ≫ (i _*).map φ) G.π) sorry

/-- The two maps of `differenceShortComplex` are `(1, -ψ)` and `(φ, 1)` on the middle biproduct. -/
theorem differenceShortComplex_spec (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    (differenceShortComplex E G φ ψ).f = biprod.lift E.ι (-((i _*).map ψ ≫ G.ι)) ∧
      (differenceShortComplex E G φ ψ).g =
        biprod.desc (E.π ≫ (i _*).map φ) G.π := sorry

/-- The middle object of `differenceExtension` is the homology of `differenceShortComplex`. -/
theorem differenceExtension_homology (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    [h : (differenceShortComplex E G φ ψ).HasHomology] :
    Nonempty ((differenceExtension E G φ ψ).E ≅
      (differenceShortComplex E G φ ψ).homology) := sorry

/-- The descended `𝒪_X`-module extension `0 ⟶ ℒ ⟶ ℋ ⟶ ℱ ⟶ 0` representing `o(φ, ψ)`.
The infinitesimal-map square is required so that the difference middle is annihilated by
`ℐ` and the descended sequence is short exact. -/
noncomputable def mapObstructionExtension (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    (hcomm : infinitesimalMap_comm E G φ ψ) :
    CategoryTheory.Extension G.kernel E.cokernel where
  E := (i ^*).obj (differenceExtension E G φ ψ).E
  f := (asIso ((pullbackPushforwardAdjunction i).counit.app G.kernel)).inv ≫
    (i ^*).map (differenceExtension E G φ ψ).f
  g := (i ^*).map (differenceExtension E G φ ψ).g ≫
    (asIso ((pullbackPushforwardAdjunction i).counit.app E.cokernel)).hom
  zero := sorry
  shortExact := sorry

/-- The left and right maps of `mapObstructionExtension` are the conjugates of the difference
extension by the pullback-pushforward counit isomorphisms. -/
theorem mapObstructionExtension_spec (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    (hcomm : infinitesimalMap_comm E G φ ψ) :
    (mapObstructionExtension E G φ ψ hcomm).E =
        (i ^*).obj (differenceExtension E G φ ψ).E ∧
      (mapObstructionExtension E G φ ψ hcomm).f =
        (asIso ((pullbackPushforwardAdjunction i).counit.app G.kernel)).inv ≫
          (i ^*).map (differenceExtension E G φ ψ).f ∧
      (mapObstructionExtension E G φ ψ hcomm).g =
        (i ^*).map (differenceExtension E G φ ψ).g ≫
          (asIso ((pullbackPushforwardAdjunction i).counit.app E.cokernel)).hom := sorry

variable [HasExt.{u} X.Modules]

/-- The obstruction class `o(φ, ψ) ∈ Ext¹_{𝒪_X}(ℱ, ℒ)` of a pair of endpoint maps whose
infinitesimal-map square commutes. -/
noncomputable def mapObstruction (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    (hcomm : infinitesimalMap_comm E G φ ψ) :
    Ext E.cokernel G.kernel 1 :=
  (mapObstructionExtension E G φ ψ hcomm).extClass

/-- `mapObstruction` is the `Ext¹` class of `mapObstructionExtension`. -/
theorem mapObstruction_eq (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    (hcomm : infinitesimalMap_comm E G φ ψ) :
    mapObstruction E G φ ψ hcomm = (mapObstructionExtension E G φ ψ hcomm).extClass := sorry

/-- After applying `i _*`, the obstruction class is the difference of the pushout of `E` along
`ψ` and the pullback of `G` along `φ`. -/
theorem mapObstruction_spec [HasExt.{u} X'.Modules]
    [(i _*).Additive] [PreservesFiniteLimits (i _*)] [PreservesFiniteColimits (i _*)]
    (E G : ModuleExtension i) (φ : E.cokernel ⟶ G.cokernel)
    (ψ : E.kernel ⟶ G.kernel) (hcomm : infinitesimalMap_comm E G φ ψ) :
    (mapObstruction E G φ ψ hcomm).mapExactFunctor (i _*) =
      (pushoutExtension E ψ).extClass - (pullbackExtension G φ).extClass := sorry

end AlgebraicGeometry.RingedSpace.Hom.ModuleExtension
