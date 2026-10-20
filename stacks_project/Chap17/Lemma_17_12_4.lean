/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
import StacksCheckRecall

@[expose] public section

/-!
# Closure properties of coherent module sheaves

The reusable statements are owned on arbitrary ringed sites.  This chapter entry records their
specialization to a ringed space and the resulting weak Serre category.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

variable (X : RingedSpace.{u})

/- Lemma 17.12.4 (01BY) (1): a finite-type submodule of a coherent module sheaf is coherent. -/
@[stacks 01BY "(1)"]
#check fun {F G : X.Modules} (f : F ⟶ G) [Mono f] [F.IsFiniteType] [G.IsCoherent] ↦
  (SheafOfModules.IsCoherent.ofMono f : F.IsCoherent)

/- Lemma 17.12.4 (01BY) (2): the kernel of a map from a finite-type module sheaf to a coherent
module sheaf is of finite type. -/
@[stacks 01BY "(2)"]
#check fun {F G : X.Modules} (f : F ⟶ G) [F.IsFiniteType] [G.IsCoherent] ↦
  (SheafOfModules.IsCoherent.kernelFiniteType f : (kernel f).IsFiniteType)

/- Lemma 17.12.4 (01BY) (3), kernel clause: coherent module sheaves are closed under
kernels. -/
@[stacks 01BY "(3), kernel"]
#check fun {F G : X.Modules} (f : F ⟶ G) [F.IsCoherent] [G.IsCoherent] ↦
  (SheafOfModules.IsCoherent.kernel f : (kernel f).IsCoherent)

/- Lemma 17.12.4 (01BY) (3), cokernel clause: coherent module sheaves are closed under
cokernels. -/
@[stacks 01BY "(3), cokernel"]
#check fun {F G : X.Modules} (f : F ⟶ G) [F.IsCoherent] [G.IsCoherent] ↦
  (SheafOfModules.IsCoherent.cokernel f : (cokernel f).IsCoherent)

/- Lemma 17.12.4 (01BY) (4), middle-term clause: in a short exact sequence, coherence of the
outer terms implies coherence of the middle term. -/
@[stacks 01BY "(4), middle term"]
#check fun {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₃.IsCoherent] ↦
  (SheafOfModules.IsCoherent.middle_of_shortExact hS : S.X₂.IsCoherent)

/- Lemma 17.12.4 (01BY) (4), left-term clause: in a short exact sequence, coherence of the
middle and right terms implies coherence of the left term. -/
@[stacks 01BY "(4), left term"]
#check fun {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₂.IsCoherent] [S.X₃.IsCoherent] ↦
  (SheafOfModules.IsCoherent.left_of_shortExact hS : S.X₁.IsCoherent)

/- Lemma 17.12.4 (01BY) (4), right-term clause: in a short exact sequence, coherence of the
left and middle terms implies coherence of the right term. -/
@[stacks 01BY "(4), right term"]
#check fun {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] ↦
  (SheafOfModules.IsCoherent.right_of_shortExact hS : S.X₃.IsCoherent)

/- Lemma 17.12.4 (01BY) (5): coherent module sheaves form a weak Serre class. -/
@[stacks 01BY "(5)"]
#check
  (inferInstance : IsWeakSerreClass (SheafOfModules.isCoherent X.ringCatSheaf))

/- Lemma 17.12.4 (01BY), consequence: the category of coherent `𝒪_X`-modules is abelian. -/
@[stacks 01BY "abelian consequence"]
#check (inferInstance : Abelian (RingedSpace.Coh X))

/- Lemma 17.12.4 (01BY), consequence: the inclusion of coherent module sheaves into all module
sheaves is exact. -/
@[stacks 01BY "exact inclusion"]
#check
  (IsWeakSerreClass.Inclusion.isExact (SheafOfModules.isCoherent X.ringCatSheaf) :
    exactFunctor (RingedSpace.Coh X) X.Modules
      (SheafOfModules.isCoherent X.ringCatSheaf).ι)
