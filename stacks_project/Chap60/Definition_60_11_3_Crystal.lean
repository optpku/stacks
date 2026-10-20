module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

open CategoryTheory

universe u v w

@[expose] public section

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A sheaf of modules is a crystal in quasi-coherent modules when it is quasi-coherent
as a sheaf of modules over the ambient ring sheaf. On crystalline sites this is equivalent
to being locally quasi-coherent and a crystal in modules. -/
class IsCrystalInQuasiCoherentModules (F : SheafOfModules.{w} R) : Prop where
  /-- Quasi-coherence of the module sheaf. -/
  isQuasicoherent : F.IsQuasicoherent

/-- Quasi-coherent module sheaves are crystals in quasi-coherent modules. -/
instance instIsCrystalInQuasiCoherentModules_of_isQuasicoherent
    (F : SheafOfModules.{w} R) [hF : F.IsQuasicoherent] :
    IsCrystalInQuasiCoherentModules F where
  isQuasicoherent := hF

/-- A crystal in quasi-coherent modules is quasi-coherent. -/
instance instIsQuasicoherent_of_isCrystalInQuasiCoherentModules
    (F : SheafOfModules.{w} R) [hF : IsCrystalInQuasiCoherentModules F] :
    F.IsQuasicoherent :=
  hF.isQuasicoherent

/-- The defining characterization of crystals in quasi-coherent modules. -/
theorem isCrystalInQuasiCoherentModules_iff (F : SheafOfModules.{w} R) :
    IsCrystalInQuasiCoherentModules F ↔ F.IsQuasicoherent := sorry

/-- A sheaf of modules is a crystal in finite locally free modules when it is a crystal
in quasi-coherent modules and is finite locally free. -/
class IsCrystalInFiniteLocallyFreeModules (F : SheafOfModules.{w} R) : Prop
    extends IsCrystalInQuasiCoherentModules F where
  /-- Finite local freeness of the module sheaf. -/
  isFiniteLocallyFree : F.IsFiniteLocallyFree

/-- Crystals in quasi-coherent modules that are finite locally free are crystals in
finite locally free modules. -/
instance instIsCrystalInFiniteLocallyFreeModules_of
    (F : SheafOfModules.{w} R) [IsCrystalInQuasiCoherentModules F] [hF : F.IsFiniteLocallyFree] :
    IsCrystalInFiniteLocallyFreeModules F where
  isFiniteLocallyFree := hF

/-- A crystal in finite locally free modules is finite locally free. -/
instance instIsFiniteLocallyFree_of_isCrystalInFiniteLocallyFreeModules
    (F : SheafOfModules.{w} R) [hF : IsCrystalInFiniteLocallyFreeModules F] :
    F.IsFiniteLocallyFree :=
  hF.isFiniteLocallyFree

/-- The defining characterization of crystals in finite locally free modules. -/
theorem isCrystalInFiniteLocallyFreeModules_iff (F : SheafOfModules.{w} R) :
    IsCrystalInFiniteLocallyFreeModules F ↔
      IsCrystalInQuasiCoherentModules F ∧ F.IsFiniteLocallyFree := sorry

/-- Joint source-semantic specification of crystals in finite locally free modules. -/
theorem IsCrystalInFiniteLocallyFreeModules.spec (F : SheafOfModules.{w} R) :
    IsCrystalInFiniteLocallyFreeModules F ↔
      F.IsQuasicoherent ∧ F.IsFiniteLocallyFree := sorry

end SheafOfModules
