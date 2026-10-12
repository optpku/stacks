/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import ReasLib.Algebra.Category.ModuleCat.Topology.Limit
public import ReasLib.CategoryTheory.InverseSystem.Positive

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u v

namespace FiniteDual

/-- The finite topology on the algebraic dual of a vector space: restriction to every
finite-dimensional subspace is continuous when the target dual is discrete. -/
@[implicit_reducible]
def topology (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V] :
    TopologicalSpace (Module.Dual k V) :=
  ⨅ W : {W : Submodule k V // FiniteDimensional k W},
    TopologicalSpace.induced W.1.dualRestrict ⊥

/-- The finite topology is the infimum of the topologies induced by restriction to
finite-dimensional subspaces. -/
theorem topology_def (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V] :
    topology k V =
      ⨅ W : {W : Submodule k V // FiniteDimensional k W},
        TopologicalSpace.induced W.1.dualRestrict ⊥ := sorry

/-- The annihilators of finite-dimensional subspaces form the neighborhood basis at zero
for the finite topology. -/
theorem topology_hasBasis (k : Type u) [Field k]
    (V : Type v) [AddCommGroup V] [Module k V] :
    (@nhds (Module.Dual k V) (topology k V) 0).HasBasis
      (fun _ : {W : Submodule k V // FiniteDimensional k W} ↦ True)
      (fun W ↦ (W.1.dualAnnihilator : Set (Module.Dual k V))) := sorry

/-- The explicit dual-system map assigned to an identity is an identity. -/
theorem diagram_map_id {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) (i : OrderDual ℕ+) :
    ModuleCat.ofHom (G.map (homOfLE (𝟙 i).le)).hom.dualMap =
      𝟙 (ModuleCat.of k (Module.Dual k (G.obj (OrderDual.ofDual i)))) := sorry

/-- The explicit dual-system maps preserve composition. -/
theorem diagram_map_comp {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) {i j l : OrderDual ℕ+}
    (f : i ⟶ j) (g : j ⟶ l) :
    ModuleCat.ofHom (G.map (homOfLE (f ≫ g).le)).hom.dualMap =
      ModuleCat.ofHom (G.map (homOfLE f.le)).hom.dualMap ≫
        ModuleCat.ofHom (G.map (homOfLE g.le)).hom.dualMap := sorry

/-- Dualizing a direct system gives the inverse system of its algebraic duals. -/
noncomputable def diagram {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) :
    PNatInverseSystem (ModuleCat.{max u v} k) where
  obj i := ModuleCat.of k (Module.Dual k (G.obj (OrderDual.ofDual i)))
  map f := ModuleCat.ofHom (G.map (homOfLE f.le)).hom.dualMap
  map_id := diagram_map_id G
  map_comp := diagram_map_comp G

/-- A stage of the dual inverse system is the algebraic dual of the corresponding
direct-system stage. -/
theorem diagram_obj {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) (i : OrderDual ℕ+) :
    (diagram G).obj i =
      ModuleCat.of k (Module.Dual k (G.obj (OrderDual.ofDual i))) := sorry

/-- The componentwise dual maps commute with the transition maps of the dual systems. -/
theorem diagramMap_naturality {k : Type u} [Field k]
    {G H : ℕ+ ⥤ ModuleCat.{max u v} k} (f : G ⟶ H)
    {i j : OrderDual ℕ+} (g : i ⟶ j) :
    (diagram H).map g ≫ ModuleCat.ofHom (f.app (OrderDual.ofDual j)).hom.dualMap =
      ModuleCat.ofHom (f.app (OrderDual.ofDual i)).hom.dualMap ≫
        (diagram G).map g := sorry

/-- A map of direct systems induces the contravariant map of their dual inverse systems. -/
noncomputable def diagramMap {k : Type u} [Field k]
    {G H : ℕ+ ⥤ ModuleCat.{max u v} k} (f : G ⟶ H) :
    diagram H ⟶ diagram G where
  app i := ModuleCat.ofHom (f.app (OrderDual.ofDual i)).hom.dualMap
  naturality := fun _ _ g ↦ diagramMap_naturality f g

/-- The component of `diagramMap` is the dual of the corresponding direct-system map. -/
theorem diagramMap_app {k : Type u} [Field k]
    {G H : ℕ+ ⥤ ModuleCat.{max u v} k} (f : G ⟶ H)
    (i : OrderDual ℕ+) :
    (diagramMap f).app i =
      ModuleCat.ofHom (f.app (OrderDual.ofDual i)).hom.dualMap := sorry

/-- The evaluation maps associated to a compatible family form a cocone on the direct
system. -/
theorem limitToDualColimit_naturality {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) [HasColimit G] [HasLimit (diagram G)]
    (x : (limit (diagram G) : ModuleCat.{max u v} k)) {i j : ℕ+} (f : i ⟶ j) :
    G.map f ≫ ModuleCat.ofHom
        ((ULift.moduleEquiv.symm.toLinearMap : k →ₗ[k] ULift.{max u v} k).comp
          ((limit.π (diagram G) (OrderDual.toDual j)).hom x)) =
      ModuleCat.ofHom
        ((ULift.moduleEquiv.symm.toLinearMap : k →ₗ[k] ULift.{max u v} k).comp
          ((limit.π (diagram G) (OrderDual.toDual i)).hom x)) ≫
        ((Functor.const ℕ+).obj (ModuleCat.of k (ULift.{max u v} k))).map f := sorry

/-- The function sending a compatible family of stagewise functionals to the induced
functional on the colimit. -/
noncomputable def limitToDualColimitFun {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) [HasColimit G] [HasLimit (diagram G)] :
    (limit (diagram G) : ModuleCat.{max u v} k) →
      Module.Dual k (colimit G : ModuleCat.{max u v} k) :=
  fun x ↦
    ULift.moduleEquiv.toLinearMap.comp
      (colimit.desc G
      { pt := ModuleCat.of k (ULift.{max u v} k)
        ι :=
          { app := fun i ↦ ModuleCat.ofHom
              (ULift.moduleEquiv.symm.toLinearMap.comp
                ((limit.π (diagram G) (OrderDual.toDual i)).hom x))
            naturality := fun _ _ f ↦ limitToDualColimit_naturality G x f } }).hom

/-- The induced functional on the colimit preserves addition of compatible families. -/
theorem limitToDualColimitFun_map_add {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) [HasColimit G] [HasLimit (diagram G)]
    (x y : (limit (diagram G) : ModuleCat.{max u v} k)) :
    limitToDualColimitFun G (x + y) =
      limitToDualColimitFun G x + limitToDualColimitFun G y := sorry

/-- The induced functional on the colimit preserves scalar multiplication. -/
theorem limitToDualColimitFun_map_smul {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) [HasColimit G] [HasLimit (diagram G)]
    (c : k) (x : (limit (diagram G) : ModuleCat.{max u v} k)) :
    limitToDualColimitFun G (c • x) = c • limitToDualColimitFun G x := sorry

/-- A compatible family of functionals on a direct system induces a functional on its
colimit. -/
noncomputable def limitToDualColimit {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) [HasColimit G] [HasLimit (diagram G)] :
    (limit (diagram G) : ModuleCat.{max u v} k) →ₗ[k]
      Module.Dual k (colimit G : ModuleCat.{max u v} k) where
  toFun := limitToDualColimitFun G
  map_add' := limitToDualColimitFun_map_add G
  map_smul' := limitToDualColimitFun_map_smul G

/-- Evaluation of the functional induced on a colimit agrees with evaluation at every
stage representative. -/
theorem limitToDualColimit_comp_ι {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) [HasColimit G]
    [HasLimit (diagram G)] (i : ℕ+) :
    (colimit.ι G i).hom.dualMap.comp (limitToDualColimit G) =
      (limit.π (diagram G) (OrderDual.toDual i)).hom := sorry

/-- Algebraic duality sends a module colimit to the limit of the dual diagram. -/
theorem limitToDualColimit_bijective {k : Type u} [Field k]
    (G : ℕ+ ⥤ ModuleCat.{max u v} k) [HasColimit G] [HasLimit (diagram G)] :
    Function.Bijective (limitToDualColimit G) := sorry

/-- The comparison from an inverse system identified with the dual of a direct system to
the dual of a chosen model of its colimit. -/
noncomputable def limitComparison {k : Type u} [Field k]
    (F : PNatInverseSystem (ModuleCat.{max u v} k))
    (G : ℕ+ ⥤ ModuleCat.{max u v} k)
    [HasLimit F] [HasColimit G] [HasLimit (diagram G)]
    (stageDuality : F ≅ diagram G) {H : ModuleCat.{max u v} k}
    (ordinaryComparison : colimit G ≅ H) :
    (limit F : ModuleCat.{max u v} k) →ₗ[k] Module.Dual k H :=
  ordinaryComparison.inv.hom.dualMap.comp
    ((limitToDualColimit G).comp (limMap stageDuality.hom).hom)

/-- The limit comparison is the composite of the limit of the stagewise dualities, the
dual-colimit comparison, and transport to the chosen ordinary-cohomology model. -/
theorem limitComparison_def {k : Type u} [Field k]
    (F : PNatInverseSystem (ModuleCat.{max u v} k))
    (G : ℕ+ ⥤ ModuleCat.{max u v} k)
    [HasLimit F] [HasColimit G] [HasLimit (diagram G)]
    (stageDuality : F ≅ diagram G) {H : ModuleCat.{max u v} k}
    (ordinaryComparison : colimit G ≅ H) :
    limitComparison F G stageDuality ordinaryComparison =
      ordinaryComparison.inv.hom.dualMap.comp
        ((limitToDualColimit G).comp (limMap stageDuality.hom).hom) := sorry

end FiniteDual
