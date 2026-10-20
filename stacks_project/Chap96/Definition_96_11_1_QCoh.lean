module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf

/-!
# Quasi-coherent modules on a category fibred in groupoids

A quasi-coherent `𝒪_𝒳`-module is a module sheaf on the fppf ringed site of a
category fibred in groupoids that is quasi-coherent in the sense of
`SheafOfModules.IsQuasicoherent`. The category of such sheaves is the
corresponding full subcategory `QCoh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- The fppf ringed site `(𝒳_fppf, 𝒪_𝒳)` of a category fibred in groupoids. -/
abbrev fppfRingedSite : RingedSite.{u + 1, u, u} :=
  X.ringedSite

#check (AlgebraicGeometry.GroupoidsOver.ringedSite_structureSheaf :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    (fppfRingedSite X).structureSheaf = structureSheaf X)

#check (AlgebraicGeometry.GroupoidsOver.quasiCoherentModuleProperty :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    ObjectProperty (RingedSite.ModuleCat.{u} (fppfRingedSite X)))

#check (AlgebraicGeometry.GroupoidsOver.QCoh :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    QCoh X ⥤ RingedSite.ModuleCat.{u} (fppfRingedSite X))

end AlgebraicGeometry.GroupoidsOver
