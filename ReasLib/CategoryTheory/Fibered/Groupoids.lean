/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Groupoids.Forgetful
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism.BaseChange
public import ReasLib.CategoryTheory.Fibered.Groupoids.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Groupoids.Pullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.FullSubbicategory
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base

/-!
# Categories fibred in groupoids

Compatibility aggregate for the bicategory owner, morphism and forgetful computation APIs,
pullback, diagonal, slice base change, the neutral full-subbicategory equivalence lift, and the
canonical universe-resized base object. New direct users should import the narrow leaf that owns
the needed construction.
-/
