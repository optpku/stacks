/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category

/-!
# Coherent modules on groupoids in algebraic spaces

An equivariant quasi-coherent module on a groupoid `(U, R, s, t, c)` in algebraic
spaces is coherent precisely when the underlying `𝒪_U`-module is coherent. The
category of such objects is the full subcategory `Coh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}

/-- An equivariant quasi-coherent module on a groupoid in algebraic spaces is
coherent when the underlying module on the object space is a coherent
`𝒪_U`-module. -/
class IsCoherent (A : G.QCoh) : Prop where
  /-- The underlying quasi-coherent module on `U` is coherent. -/
  obj_isCoherent : A.obj.obj.IsCoherent

/-- Coherence of the underlying `𝒪_U`-module yields coherence of the equivariant
pair. -/
instance instIsCoherent_of_obj (A : G.QCoh) [A.obj.obj.IsCoherent] : IsCoherent A where
  obj_isCoherent := inferInstance

/-- An equivariant quasi-coherent module is coherent if and only if the
underlying `𝒪_U`-module is coherent. -/
theorem isCoherent_iff (A : G.QCoh) :
    IsCoherent A ↔ A.obj.obj.IsCoherent :=
  sorry

/-- The object property of coherent equivariant quasi-coherent modules on a
groupoid in algebraic spaces. -/
abbrev coherentModuleProperty (G : GroupoidAlgebraicSpace B) : ObjectProperty G.QCoh :=
  IsCoherent

/-- `coherentModuleProperty G` is the groupoid-level coherence class. -/
theorem coherentModuleProperty_eq (G : GroupoidAlgebraicSpace B) :
    coherentModuleProperty G = IsCoherent :=
  sorry

/-- An object of `G.QCoh` lies in `coherentModuleProperty G` if and only if it is
coherent. -/
theorem mem_Coh_iff (A : G.QCoh) :
    coherentModuleProperty G A ↔ IsCoherent A :=
  sorry

/-- The category `Coh(U, R, s, t, c)` of coherent equivariant modules on a
groupoid in algebraic spaces. -/
abbrev Coh (G : GroupoidAlgebraicSpace B) :=
  (coherentModuleProperty G).FullSubcategory

namespace Coh

/-- The inclusion of coherent equivariant modules into all equivariant
quasi-coherent modules. -/
abbrev inclusion (G : GroupoidAlgebraicSpace B) : Coh G ⥤ G.QCoh :=
  (coherentModuleProperty G).ι

/-- The inclusion of `Coh G` forgets only the coherence predicate. -/
theorem inclusion_obj (A : Coh G) : (inclusion G).obj A = A.obj :=
  sorry

end Coh

end AlgebraicGeometry.GroupoidAlgebraicSpace
