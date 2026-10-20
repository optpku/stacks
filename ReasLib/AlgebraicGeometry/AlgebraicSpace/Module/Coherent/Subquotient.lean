/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

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
