/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.MappingCone.Triangle

/-!
# Functoriality of differential graded mapping cones

A commutative square of differential graded module maps induces the block-diagonal map between
the corresponding mapping cones.  This file records its coordinate, identity, composition, and
triangle-morphism APIs, both before and after passage to the DG homotopy category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.MappingCone

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable {𝒜 : DGA(𝒪)}
variable {K L K' L' K'' L'' : Mod(𝒜, d)}
variable {f : K ⟶ L} {g : K' ⟶ L'} {h : K'' ⟶ L''}
variable {a : K ⟶ K'} {b : L ⟶ L'} {a' : K' ⟶ K''} {b' : L' ⟶ L''}

/-- The degree-`n` block-diagonal map between mapping-cone terms induced by a commutative
square.  In the ordering `Lⁿ ⨞ Kⁿ⁺¹`, its diagonal entries are `bⁿ` and `aⁿ⁺¹`. -/
noncomputable def mapComponent (_ : CommSq f a b g) (n : ℤ) :
    (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone f).toComplex.X n ⟶
      (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone g).toComplex.X n :=
  biprod.map (b.toCochainMap.f n) (a.toCochainMap.f (n + 1))

/-- The block-diagonal cone components commute with the mapping-cone differentials. -/
theorem mapComponent_comm (sq : CommSq f a b g) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    mapComponent sq i ≫
        (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone g).toComplex.d i j =
      (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone f).toComplex.d i j ≫
        mapComponent sq j := sorry

/-- The underlying cochain map between mapping cones induced by a commutative square. -/
noncomputable def underlyingMap (sq : CommSq f a b g) :
    (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone f).toComplex ⟶
      (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone g).toComplex where
  f := mapComponent sq
  comm' := mapComponent_comm sq

/-- The block-diagonal cone map is compatible with the differential graded algebra action. -/
theorem mapComponent_smul (sq : CommSq f a b g) (n m : ℤ) :
    (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone f).smul n m ≫
        mapComponent sq (n + m) =
      ((mapComponent sq n) ▷ 𝒜.toComplex.X m) ≫
        (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone g).smul n m := sorry

/-- The morphism between differential graded mapping cones induced by a commutative square. -/
noncomputable def map (sq : CommSq f a b g) :
    _root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone f ⟶
      _root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone g where
  toCochainMap := underlyingMap sq
  comm := mapComponent_smul sq

/-- The degree-`n` component of the mapping-cone map is the expected block-diagonal map. -/
@[simp]
theorem map_f (sq : CommSq f a b g) (n : ℤ) :
    (map sq).toCochainMap.f n =
      biprod.map (b.toCochainMap.f n) (a.toCochainMap.f (n + 1)) := sorry

/-- The degree-`-1` source inclusion is natural with respect to mapping-cone maps. -/
theorem inl_map (sq : CommSq f a b g) :
    gradedHomComp (homToCompHom (map sq)).val (inl f) =
      gradedHomComp (inl g) (homToCompHom a).val := sorry

/-- The degree-zero target inclusion is natural with respect to mapping-cone maps. -/
theorem inrGraded_map (sq : CommSq f a b g) :
    gradedHomComp (homToCompHom (map sq)).val (inrGraded f) =
      gradedHomComp (inrGraded g) (homToCompHom b).val := sorry

/-- The degree-one source projection is natural with respect to mapping-cone maps. -/
theorem map_fst (sq : CommSq f a b g) :
    gradedHomComp (fst g) (homToCompHom (map sq)).val =
      gradedHomComp (homToCompHom a).val (fst f) := sorry

/-- The degree-zero target projection is natural with respect to mapping-cone maps. -/
theorem map_snd (sq : CommSq f a b g) :
    gradedHomComp (snd g) (homToCompHom (map sq)).val =
      gradedHomComp (homToCompHom b).val (snd f) := sorry

/-- The commutative square remains commutative after forgetting to cochain complexes. -/
theorem toCochainMap_square (sq : CommSq f a b g) :
    f.toCochainMap ≫ b.toCochainMap = a.toCochainMap ≫ g.toCochainMap := sorry

/-- The explicit block-diagonal cone map agrees, through the canonical cone comparisons, with
Mathlib's map between cochain-complex mapping cones. -/
theorem map_toCochainMappingCone (sq : CommSq f a b g) :
    (map sq).toCochainMap ≫
        (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingConeToCochainMappingCone
          g).hom =
      (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingConeToCochainMappingCone
          f).hom ≫
        CochainComplex.mappingCone.map f.toCochainMap g.toCochainMap
          a.toCochainMap b.toCochainMap (toCochainMap_square sq) := sorry

/-- Mapping-cone maps preserve the canonical target inclusion. -/
@[reassoc]
theorem inr_map (sq : CommSq f a b g) :
    inr f ≫ map sq = b ≫ inr g := sorry

/-- Mapping-cone maps preserve the projection to the shifted source. -/
@[reassoc]
theorem map_toShift (sq : CommSq f a b g) :
    map sq ≫ toShift g = toShift f ≫ Shift.map a 1 := sorry

/-- Mapping-cone maps preserve the projection to the shifted source, expressed using the
ambient categorical shift. -/
theorem toShift_map_shift (sq : CommSq f a b g) :
    toShift f ≫ a⟦(1 : ℤ)⟧' = map sq ≫ toShift g := sorry

/-- The cone map associated to an identity square is the identity. -/
@[simp]
theorem map_id (f : K ⟶ L) (sq : CommSq f (𝟙 K) (𝟙 L) f) :
    map sq = 𝟙 (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone f) := sorry

/-- Mapping-cone maps preserve vertical composition of commutative squares. -/
@[reassoc]
theorem map_comp (sq : CommSq f a b g) (sq' : CommSq g a' b' h) :
    map (CommSq.vert_comp sq sq') = map sq ≫ map sq' := sorry

/-- A commutative square induces a morphism between the associated module-level mapping-cone
triangles. -/
noncomputable def triangleMap (sq : CommSq f a b g) : triangle f ⟶ triangle g where
  hom₁ := a
  hom₂ := b
  hom₃ := map sq
  comm₁ := sq.w
  comm₂ := inr_map sq
  comm₃ := toShift_map_shift sq

/-- The first component of the induced mapping-cone triangle morphism is the source map. -/
@[simp]
theorem triangleMap_hom₁ (sq : CommSq f a b g) : (triangleMap sq).hom₁ = a := sorry

/-- The second component of the induced mapping-cone triangle morphism is the target map. -/
@[simp]
theorem triangleMap_hom₂ (sq : CommSq f a b g) : (triangleMap sq).hom₂ = b := sorry

/-- The third component of the induced mapping-cone triangle morphism is the cone map. -/
@[simp]
theorem triangleMap_hom₃ (sq : CommSq f a b g) : (triangleMap sq).hom₃ = map sq := sorry

/-- The triangle morphism associated to an identity square is the identity. -/
@[simp]
theorem triangleMap_id (f : K ⟶ L) (sq : CommSq f (𝟙 K) (𝟙 L) f) :
    triangleMap sq = 𝟙 (triangle f) := sorry

/-- Mapping-cone triangle morphisms preserve vertical composition of commutative squares. -/
@[reassoc]
theorem triangleMap_comp (sq : CommSq f a b g) (sq' : CommSq g a' b' h) :
    triangleMap (CommSq.vert_comp sq sq') = triangleMap sq ≫ triangleMap sq' := sorry

/-- The morphism of mapping-cone triangles induced in the DG homotopy category. -/
noncomputable def triangleMapK (sq : CommSq f a b g) : triangleK f ⟶ triangleK g :=
  (toK 𝒜).mapTriangle.map (triangleMap sq)

/-- The first component of the induced homotopy-category triangle morphism is the image of the
source map. -/
@[simp]
theorem triangleMapK_hom₁ (sq : CommSq f a b g) :
    (triangleMapK sq).hom₁ = (toK 𝒜).map a := sorry

/-- The second component of the induced homotopy-category triangle morphism is the image of the
target map. -/
@[simp]
theorem triangleMapK_hom₂ (sq : CommSq f a b g) :
    (triangleMapK sq).hom₂ = (toK 𝒜).map b := sorry

/-- The third component of the induced homotopy-category triangle morphism is the image of the
cone map. -/
@[simp]
theorem triangleMapK_hom₃ (sq : CommSq f a b g) :
    (triangleMapK sq).hom₃ = (toK 𝒜).map (map sq) := sorry

/-- The homotopy-category triangle morphism associated to an identity square is the identity. -/
@[simp]
theorem triangleMapK_id (f : K ⟶ L) (sq : CommSq f (𝟙 K) (𝟙 L) f) :
    triangleMapK sq = 𝟙 (triangleK f) := sorry

/-- Homotopy-category mapping-cone triangle morphisms preserve vertical composition of
commutative squares. -/
@[reassoc]
theorem triangleMapK_comp (sq : CommSq f a b g) (sq' : CommSq g a' b' h) :
    triangleMapK (CommSq.vert_comp sq sq') = triangleMapK sq ≫ triangleMapK sq' := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule.MappingCone

-- The only `sorryAx` in these data owners is confined to cochain, action, and triangle
-- commutativity fields; all degreewise morphism data is the displayed block-diagonal map.

end
