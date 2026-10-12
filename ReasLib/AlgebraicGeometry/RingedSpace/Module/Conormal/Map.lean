/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Conormal sheaves and comparison maps on ringed spaces

The conormal sheaf of a morphism of ringed spaces is the kernel-cotangent sheaf of its
inverse-image structure-sheaf map. A commutative square induces a canonical pullback comparison,
whose sectionwise construction applies the ambient coefficient map to kernel representatives.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {Z X Z' X' : RingedSpace.{u}}

/-- The conormal sheaf of a morphism of ringed spaces, formed from the kernel cotangent module of
its inverse-image structure-sheaf map. -/
noncomputable abbrev conormalSheaf (i : Z ⟶ X) : Z.Modules :=
  conormalSource (J := Opens.grothendieckTopology Z)
    (O₂ := (TopCat.Sheaf.pullback CommRingCat.{u} i.hom.base).obj X.sheaf)
    (O₃ := Z.sheaf) (inverseImageStructureSheafHomComm i)

namespace Conormal

variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}

/-- The inverse-image structure-sheaf maps in a commutative square form a commutative square
after pushing the lower map forward. -/
theorem structureSquare (sq : CommSq f i i' g) :
    let middle :=
      ((TopCat.Sheaf.pullbackPushforwardAdjunction
        CommRingCat.{u} f.hom.base).homEquiv _ _)
        ((StructureSheaf.compIso f i').hom ≫
          (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
            (congrArg (fun k : Z ⟶ X' ↦ k.hom.base) sq.w)).hom.app X'.sheaf ≫
          (StructureSheaf.compIso i g).inv ≫
          (TopCat.Sheaf.pullback CommRingCat.{u} i.hom.base).map
            (inverseImageStructureSheafHomComm g))
    CommSq middle (inverseImageStructureSheafHomComm i')
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        (inverseImageStructureSheafHomComm i))
      (commRingSheafPushforwardMap f) := sorry

/-- The canonical pullback comparison between the conormal sheaves in a commutative square of
ringed spaces. -/
noncomputable def map (sq : CommSq f i i' g) :
    (RingedSpace.Hom.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i :=
  let middle :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} f.hom.base).homEquiv _ _)
      ((StructureSheaf.compIso f i').hom ≫
        (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
          (congrArg (fun k : Z ⟶ X' ↦ k.hom.base) sq.w)).hom.app X'.sheaf ≫
        (StructureSheaf.compIso i g).inv ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} i.hom.base).map
          (inverseImageStructureSheafHomComm g))
  SheafOfModules.RingedSite.Conormal.InverseImage.comparison
    (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
    (Opens.map f.hom.base) middle (commRingSheafPushforwardMap f)
      (structureSquare sq)

/-- A conormal comparison morphism is characterized by having the explicit adjoint comparison
induced from the structure-sheaf square. -/
def IsMap (sq : CommSq f i i' g)
    (tau : (RingedSpace.Hom.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i) : Prop :=
  let middle :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} f.hom.base).homEquiv _ _)
      ((StructureSheaf.compIso f i').hom ≫
        (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
          (congrArg (fun k : Z ⟶ X' ↦ k.hom.base) sq.w)).hom.app X'.sheaf ≫
        (StructureSheaf.compIso i g).inv ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} i.hom.base).map
          (inverseImageStructureSheafHomComm g))
  (RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv _ _ tau =
    SheafOfModules.RingedSite.Conormal.InverseImage.comparisonAdjoint
      (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
      (Opens.map f.hom.base) middle (commRingSheafPushforwardMap f)
        (structureSquare sq)

/-- On a cotangent generator, the sectionwise comparison applies the coefficient map to the
kernel representative. -/
theorem map_toCotangent (sq : CommSq f i i' g) (U : (Opens Z')ᵒᵖ)
    (x : conormalIdeal (inverseImageStructureSheafHomComm i') U) :
    let middle :=
      ((TopCat.Sheaf.pullbackPushforwardAdjunction
        CommRingCat.{u} f.hom.base).homEquiv _ _)
        ((StructureSheaf.compIso f i').hom ≫
          (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
            (congrArg (fun k : Z ⟶ X' ↦ k.hom.base) sq.w)).hom.app X'.sheaf ≫
          (StructureSheaf.compIso i g).inv ≫
          (TopCat.Sheaf.pullback CommRingCat.{u} i.hom.base).map
            (inverseImageStructureSheafHomComm g))
    SheafOfModules.RingedSite.Conormal.InverseImage.comparisonApp
        (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
        (Opens.map f.hom.base) middle (commRingSheafPushforwardMap f)
        (structureSquare sq) U
        ((conormalIdeal (inverseImageStructureSheafHomComm i') U).toCotangent x) =
      ((conormalSourcePresheafUnit (inverseImageStructureSheafHomComm i)).app
        ((Opens.map f.hom.base).op.obj U))
        ((conormalIdeal (inverseImageStructureSheafHomComm i)
          ((Opens.map f.hom.base).op.obj U)).toCotangent
          ⟨(middle.hom.app U).hom x,
            SheafOfModules.RingedSite.Conormal.InverseImage.ideal_le_comap
              (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
              (Opens.map f.hom.base) middle (commRingSheafPushforwardMap f)
              (structureSquare sq) U x.2⟩) :=
  let middle :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} f.hom.base).homEquiv _ _)
      ((StructureSheaf.compIso f i').hom ≫
        (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
          (congrArg (fun k : Z ⟶ X' ↦ k.hom.base) sq.w)).hom.app X'.sheaf ≫
        (StructureSheaf.compIso i g).inv ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} i.hom.base).map
          (inverseImageStructureSheafHomComm g))
  SheafOfModules.RingedSite.Conormal.InverseImage.comparisonApp_toCotangent
    (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
    (Opens.map f.hom.base) middle (commRingSheafPushforwardMap f)
      (structureSquare sq) U x

/-- The canonical conormal comparison satisfies its adjoint characterization. -/
theorem map_isMap (sq : CommSq f i i' g) : IsMap sq (map sq) :=
  let middle :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} f.hom.base).homEquiv _ _)
      ((StructureSheaf.compIso f i').hom ≫
        (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
          (congrArg (fun k : Z ⟶ X' ↦ k.hom.base) sq.w)).hom.app X'.sheaf ≫
        (StructureSheaf.compIso i g).inv ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} i.hom.base).map
          (inverseImageStructureSheafHomComm g))
  SheafOfModules.RingedSite.Conormal.InverseImage.comparison_adj
    (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
    (Opens.map f.hom.base) middle (commRingSheafPushforwardMap f)
      (structureSquare sq)

/-- A conormal comparison satisfying the adjoint characterization is the canonical map. -/
theorem eq_map (sq : CommSq f i i' g)
    {tau : (RingedSpace.Hom.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i}
    (h_tau : IsMap sq tau) : tau = map sq := sorry

/-- A commutative square of ringed spaces has a unique conormal comparison satisfying the
adjoint characterization. -/
theorem existsUnique_map (sq : CommSq f i i' g) :
    ∃! tau : (RingedSpace.Hom.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i,
      IsMap sq tau :=
  ⟨map sq, map_isMap sq, fun tau h_tau ↦ eq_map sq h_tau⟩

end Conormal

end AlgebraicGeometry.RingedSpace.Hom
