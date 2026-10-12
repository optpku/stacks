/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Coherence of subquotients on algebraic spaces

Coherent modules on a locally Noetherian algebraic space are closed under
quasi-coherent subobjects and quotients.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]

/-- A quasi-coherent subobject of a coherent module on a locally Noetherian algebraic space is
coherent. -/
theorem isCoherent_subobject_of_isQuasicoherent
    (F : X.Modules) [F.IsCoherent] (G : Subobject F)
    [((G : X.Modules)).IsQuasicoherent] :
    ((G : X.Modules)).IsCoherent := sorry

/-- A quasi-coherent quotient of a coherent module on a locally Noetherian algebraic space is
coherent. -/
theorem isCoherent_of_epi_from_coherent
    {F G : X.Modules} [F.IsCoherent] [G.IsQuasicoherent]
    (π : F ⟶ G) [Epi π] :
    G.IsCoherent := sorry

/-- A quasi-coherent module which admits a monomorphism into a coherent module on a locally
Noetherian algebraic space is coherent. -/
theorem isCoherent_of_mono_to_coherent
    {F G : X.Modules} [G.IsCoherent] [F.IsQuasicoherent]
    (ι : F ⟶ G) [Mono ι] :
    F.IsCoherent := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
