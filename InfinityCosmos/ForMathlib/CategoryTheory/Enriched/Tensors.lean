/-
Copyright (c) ? All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ? and Arnoud van der Leer
-/

import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.MonoidalProdCat
import Mathlib.CategoryTheory.Enriched.Opposite
import Mathlib.CategoryTheory.Closed.Enrichment

/-!
  # Tensors in an enriched category

  Let `C` be a `V`-enriched category.

  This file defines a pretensor of `v : V` and `c : C` as an object `obj : C`, together with a
  morphism `cone : v ⟶ (x ⟶[V] obj)`.
  Based on this, it defines a family of morphisms `coneNatTrans : (obj ⟶[V] y) ⟶ (x ⟶[V] y)^v`.

  It defines a tensor "`v ⊗ c`" as a pretensor where the `coneNatTrans` morphisms are isomorphisms.
  Subsequently, it constructs the left and right whiskering of morphisms.

  Most of this file is devoted to showing that tensoring, together with whiskering, constitutes
  a V-enriched functor `tensor_bifunc : V ⊗ C ⟶ C`.
-/

universe u u₁ v w

open CategoryTheory MonoidalCategory MonoidalClosed BraidedCategory SymmetricCategory

open scoped MonoidalClosed

namespace CategoryTheory

namespace Enriched


-- Copied "notation" from Cotensors
abbrev Ihom (V : Type u) [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V] (x y : V) : V :=
  (ihom x).obj y

@[nolint unusedArguments]
abbrev Ehom (V : Type u) [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V]
    (C : Type v) [EnrichedCategory V C] (x y : C) : V :=
  @EnrichedCategory.Hom V _ _ _ _ x y

-- New stuff
variable {V : Type u} [Category.{u₁, u} V] [MonoidalCategory V]
  [MonoidalClosed V]
variable {C : Type v} [EnrichedCategory V C]

/-- A pretensor is an object `obj : C`, together with a morphism `cone : v ⟶ (x ⟶[V] obj)`. -/
structure Pretensor (v : V) (x : C) where
  obj : C
  cone : v ⟶ (Ehom V C x obj)

/-- The family of morphisms from `vx ⟶[V] y` to `(x ⟶[V] y)^v` -/
def Pretensor.coneNatTrans {v : V} {x : C} (vx : Pretensor v x) (y : C) :
  (Ehom V C vx.obj y) ⟶ (Ihom V v (Ehom V C x y)) :=
  curry (vx.cone ▷ Ehom V C vx.obj y ≫ eComp V x vx.obj y)

/-- Since `Pretensor.coneNatTrans` is defined by currying, its uncurrying can be simplified. -/
lemma Pretensor.uncurry_coneNatTrans {v : V} {x : C} (vx : Pretensor v x) (y : C)
  : uncurry (vx.coneNatTrans y) = vx.cone ▷ _ ≫ eComp V x vx.obj y :=
  uncurry_curry _

/-- A `Tensor` is a `Pretensor` such that `coneNatTransInv` is an inverse to `coneNatTrans`. -/
structure Tensor (v : V) (x : C) extends (Pretensor v x) where
  coneNatTransInv (y : C) :
    (Ihom V v (Ehom V C x y)) ⟶ (Ehom V C obj y)
  NatTransInv_NatTrans_eq (y : C) :
    (coneNatTransInv y ≫ Pretensor.coneNatTrans toPretensor y = 𝟙 _)
  NatTrans_NatTransInv_eq (y : C) :
    (Pretensor.coneNatTrans toPretensor y ≫ coneNatTransInv y = 𝟙 _)

/-- For a tensor, the morphisms `Pretensor.coneNatTrans` are isomorphisms, with inverses given by
  `Tensor.coneNatTransInv`. -/
instance {v : V} {x : C} {vx : Tensor v x} {y : C} : IsIso (vx.coneNatTrans y) where
  out := ⟨vx.coneNatTransInv y, {
    left := vx.NatTrans_NatTransInv_eq y
    right := vx.NatTransInv_NatTrans_eq y
  }⟩

/-- For a tensor, the morphisms `Tensor.coneNatTransInv` are isomorphisms, with inverses given by
  `Pretensor.coneNatTrans`. -/
instance {v : V} {x : C} {vx : Tensor v x} {y : C} : IsIso (vx.coneNatTransInv y) where
  out := ⟨vx.coneNatTrans y, {
    left := vx.NatTransInv_NatTrans_eq y
    right := vx.NatTrans_NatTransInv_eq y
  }⟩

namespace Tensor

variable (V : Type u) [Category.{u₁} V] [MonoidalCategory V] [MonoidalClosed V]
variable {C : Type v} [EnrichedCategory V C]

/-- Whiskering on the right by `x : C` turns a morphism `v ⟶ w` into a morphism `v ⊗ x ⟶ w ⊗ x`. -/
def whiskerRight {x : C} {v w : V} (vx : Tensor v x) (wx : Tensor w x)
  : Ehom V V v w ⟶ Ehom V C vx.obj wx.obj :=
  (ihom v).map wx.cone ≫ vx.coneNatTransInv _

/-- Since right whiskering is defined by postcomposition with `Tensor.coneNatTransInv`,
  its postcomposition with `Pretensor.coneNatTrans` can be simplified. -/
lemma whiskerRight_coneNatTrans
  {v w : V} {x : C} (vx : Tensor v x) (wx : Tensor w x)
  : whiskerRight V vx wx ≫ vx.coneNatTrans _ = (ihom v).map wx.cone
  := by
  unfold whiskerRight
  rw [Category.assoc]
  rw [vx.NatTransInv_NatTrans_eq]
  rw [Category.comp_id]

/-- Whiskering the identity on the right yields the identity again. -/
lemma whiskerRight_id
  {v : V} {x : C} (vx : Tensor v x)
  : eId V v ≫ whiskerRight V vx vx = eId V vx.obj
  := by
  -- Move vx.coneNatTrans to the RHS
  unfold whiskerRight
  rw [← Category.assoc]
  rw [← IsIso.eq_comp_inv (vx.coneNatTransInv vx.obj)]
  rw [IsIso.inv_eq_of_hom_inv_id (vx.NatTransInv_NatTrans_eq _)]
  -- Turn eId with eComp into ρ
  unfold Pretensor.coneNatTrans
  rw [← curry_natural_left]
  rw [whisker_exchange_assoc]
  rw [← Iso.hom_inv_id_assoc (ρ_ _) (_ ≫ eComp _ _ _ _)]
  rw [e_comp_id]
  rw [Category.comp_id]
  -- Move vx.cone to the right of curry, and turn curry ρ into eId
  rw [rightUnitor_naturality (vx.cone)]
  rw [curry_natural_right]
  rw [← MonoidalClosed.id_eq]
  rfl

/-- An auxiliary lemma for what is to come. -/
lemma cone_comp_whiskerRight_eq {x : C} {w v : V} (wx : Tensor w x) (vx : Tensor v x) :
  (wx.cone ⊗ₘ whiskerRight V wx vx) ≫ eComp V _ _ _
  = (ihom.ev w).app v ≫ vx.cone
  := by
  -- Remove an instance of w ◁ (ihom w).map vx from both sides
  rw [tensorHom_def'_assoc]
  rw [← ihom.ev_naturality]
  unfold whiskerRight
  rw [whiskerLeft_comp_assoc]
  apply whisker_eq
  -- Move w ◁ wx.coneNatTrans to the RHS
  rw [← IsIso.eq_inv_comp]
  rw [inv_whiskerLeft]
  rw [IsIso.inv_eq_of_hom_inv_id (wx.NatTransInv_NatTrans_eq _)]
  -- The resulting RHS is uncurry (curry (LHS))
  rw [← uncurry_eq]
  rw [wx.uncurry_coneNatTrans]

/-- Whiskering on the right commutes with morphism composition. -/
lemma whiskerRight_comp {u v w : V} {x : C} (ux : Tensor u x) (vx : Tensor v x) (wx : Tensor w x)
  : eComp V u v w ≫ whiskerRight V ux wx
    = (whiskerRight V ux vx ⊗ₘ whiskerRight V vx wx) ≫ eComp V ux.obj vx.obj wx.obj
  := by
  -- Move coneNatTrans to the RHS
  show (_ ≫ _ ≫ _ = _)
  rw [← Category.assoc]
  rw [← IsIso.eq_comp_inv (ux.coneNatTransInv wx.obj)]
  rw [IsIso.inv_eq_of_hom_inv_id (ux.NatTransInv_NatTrans_eq _)]
  rw [Category.assoc]
  -- Move the curry from coneNatTrans to around eComp
  unfold Pretensor.coneNatTrans
  repeat rw [← curry_natural_left]
  rw [eq_curry_iff]
  rw [uncurry_natural_right]
  -- eComp contains a curry, which we can cancel with the uncurry
  show (uncurry (curry ((α_ _ (Ehom _ _ _ _) (Ehom _ _ _ _)).inv ≫ _)) ≫ _ = _)
  rw [uncurry_curry]
  repeat rw [Category.assoc]
  -- Split the tensored morphism into two whiskers, and move them
  rw [tensorHom_def']
  rw [whiskerLeft_comp_assoc]
  rw [whisker_exchange_assoc]
  -- Move the associator to the RHS and use associativity on _ ◁ eComp V ux vx wx ≫ eComp V x ux wx
  rw [Iso.inv_comp_eq]
  rw [← associator_naturality_right_assoc]
  rw [← associator_naturality_middle_assoc]
  rw [← associator_naturality_left_assoc]
  rw [e_assoc']
  -- Use cone_comp_whiskerRight_eq a first time
  rw [← comp_whiskerRight_assoc (ux.cone ▷ _)]
  rw [← comp_whiskerRight_assoc]
  rw [← tensorHom_def'_assoc (ux.cone)]
  rw [cone_comp_whiskerRight_eq]
  rw [comp_whiskerRight_assoc]
  -- Use cone_comp_whiskerRight_eq a second time
  rw [whisker_exchange_assoc]
  rw [← tensorHom_def'_assoc]
  rw [cone_comp_whiskerRight_eq]
  rfl

-- We only need symmetry on V for whiskerLeft and everything that follows from it
variable [SymmetricCategory V]

/-- Whiskering on the left by `v : V` turns a morphism `x ⟶ y` into a morphism `v ⊗ x ⟶ v ⊗ y`. -/
def whiskerLeft {x y : C} {v : V} (vx : Tensor v x) (vy : Tensor v y)
  : Ehom V C x y ⟶ Ehom V C vx.obj vy.obj :=
  curry ((β_ _ _).hom ≫ _ ◁ vy.cone ≫ eComp _ _ _ _) ≫ vx.coneNatTransInv _

/-- Since left whiskering is defined by postcomposition with `Tensor.coneNatTransInv`,
  its postcomposition with `Pretensor.coneNatTrans` can be simplified. -/
lemma whiskerLeft_coneNatTrans_eq {x y : C} {v : V} (vx : Tensor v x) (vy : Tensor v y)
  : whiskerLeft V vx vy ≫ vx.coneNatTrans _ = curry ((β_ _ _).hom ≫ _ ◁ vy.cone ≫ eComp V _ _ _)
  := by
  unfold whiskerLeft
  rw [Category.assoc]
  rw [vx.NatTransInv_NatTrans_eq]
  apply Category.comp_id

/-- Whiskering the identity on the left yields the identity again. -/
lemma whiskerLeft_id {v : V} {x : C} (vx : Tensor v x)
  : eId V x ≫ whiskerLeft V vx vx = eId V (vx.obj)
  := by
  unfold whiskerLeft
  rw [← Category.assoc]
  rw [← IsIso.eq_comp_inv (vx.coneNatTransInv vx.obj)]
  rw [IsIso.inv_eq_of_hom_inv_id (vx.NatTransInv_NatTrans_eq _)]
  unfold Pretensor.coneNatTrans
  repeat rw [← curry_natural_left]
  congrm curry ?_
  rw [braiding_naturality_right_assoc]
  rw [braiding_tensorUnit_right]
  rw [Category.assoc]
  rw [← Iso.eq_inv_comp _]
  rw [← whisker_exchange_assoc (eId _ _), whisker_exchange_assoc _ (eId _ _)]
  rw [← leftUnitor_inv_naturality_assoc, ← rightUnitor_inv_naturality_assoc]
  rw [e_id_comp, e_comp_id]

/-- An auxiliary lemma for what is to come. -/
lemma cone_comp_whiskerLeft_eq {x y : C} {v : V} (vx : Tensor v x) (vy : Tensor v y)
  : (β_ _ _).hom ≫ (vx.cone ⊗ₘ whiskerLeft V vx vy) ≫ eComp V x vx.obj vy.obj
    = Ehom V C x y ◁ vy.cone ≫ eComp V x y vy.obj
  := by
  rw [← Iso.eq_inv_comp]
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  rw [tensorHom_def'_assoc]
  rw [← Pretensor.uncurry_coneNatTrans]
  rw [← uncurry_natural_left]
  rw [whiskerLeft_coneNatTrans_eq]
  apply uncurry_curry

/-- Whiskering on the left commutes with morphism composition. -/
lemma whiskerLeft_comp {v : V} {x y z : C} (vx : Tensor v x) (vy : Tensor v y) (vz : Tensor v z)
  : eComp V x y z ≫ whiskerLeft V vx vz
    = (whiskerLeft V vx vy ⊗ₘ whiskerLeft V vy vz) ≫ eComp V vx.obj vy.obj vz.obj
  := by
  -- Move vx.coneNatTrans to the RHS
  show (_ ≫ _ ≫ _ = _)
  rw [← Category.assoc]
  rw [← IsIso.eq_comp_inv (vx.coneNatTransInv vz.obj)]
  rw [IsIso.inv_eq_of_hom_inv_id (vx.NatTransInv_NatTrans_eq _)]
  -- Work the LHS
  rw [← curry_natural_left]
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  -- Work the RHS
  unfold Pretensor.coneNatTrans
  rw [← curry_natural_left]
  congrm curry ?_
  -- Turn β_ into a bunch of α_ and β_ morphisms on the RHS
  rw [← Iso.eq_inv_comp]
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  rw [braiding_tensor_left_hom_assoc]
  -- Split whiskerLeft _ vx vy ⊗ₘ whiskerLeft _ vy vz
  rw [tensorHom_def_assoc]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  -- Get rid of one α_, together with a v ◁ eComp V vx vy vz
  rw [whisker_exchange_assoc _ (eComp V vx.obj vy.obj vz.obj)]
  rw [← associator_naturality_middle_assoc]
  rw [← associator_naturality_right_assoc]
  rw [← associator_naturality_left_assoc]
  rw [e_assoc']
  -- Get rid of one β_, together with a v ◁ whiskerLeft V vy vz
  rw [whisker_exchange_assoc _ (whiskerLeft _ _ _)]
  rw [whisker_exchange_assoc _ (whiskerLeft _ _ _)]
  rw [← comp_whiskerRight_assoc (vx.cone ▷ _)]
  rw [← comp_whiskerRight_assoc (v ◁ whiskerLeft _ _ _)]
  rw [← comp_whiskerRight_assoc (β_ _ _).hom]
  rw [← tensorHom_def'_assoc vx.cone (whiskerLeft _ _ _)]
  rw [cone_comp_whiskerLeft_eq]
  rw [comp_whiskerRight_assoc]
  -- Get rid of one α_, together with a eComp V x y vy.obj ▷ Ehom V C y z
  rw [← whisker_exchange_assoc (eComp V x y vy.obj)]
  rw [← associator_inv_naturality_middle_assoc]
  rw [← associator_inv_naturality_right_assoc]
  rw [e_assoc]
  -- Use cone_comp_whiskerLeft_eq
  rw [← whiskerLeft_comp_assoc _ (_ ◁ whiskerLeft _ _ _)]
  rw [← whiskerLeft_comp_assoc _ (vy.cone ▷ _)]
  rw [← whiskerLeft_comp_assoc _ (β_ _ _).hom]
  rw [← tensorHom_def_assoc vy.cone (whiskerLeft _ _ _)]
  rw [cone_comp_whiskerLeft_eq]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  -- Get rid of the last α_
  rw [← associator_naturality_right_assoc]
  rw [e_assoc']

/-- Right whiskering commutes with left whiskering. -/
lemma whiskerRight_right_eq_whiskerLeft_left {v w : V} {x y : C} (vx : Tensor v x) (wx : Tensor w x) (vy : Tensor v y) (wy : Tensor w y)
  : (whiskerRight V vx wx ⊗ₘ whiskerLeft V wx wy) ≫ eComp V vx.obj wx.obj wy.obj
    = (whiskerRight V vy wy ⊗ₘ whiskerLeft V vx vy) ≫
      (β_ _ _).hom ≫ eComp V vx.obj vy.obj wy.obj
  := by
  -- Move β to the left of the RHS
  rw [braiding_naturality_assoc]
  -- Split the tensored morphisms into double whiskers
  rw [tensorHom_def'_assoc]
  rw [tensorHom_def'_assoc]
  -- Add coneNatTrans to the end, get everything inside its curry and remove the curry
  rw [← cancel_mono (vx.coneNatTrans _)]
  repeat rw [Category.assoc _ _ (vx.coneNatTrans wy.obj)]
  unfold Pretensor.coneNatTrans
  repeat rw [← curry_natural_left]
  apply congr_arg curry
  -- On both sides: Reassociate _ ◁ eComp ≫ eComp, which gives an α, allows us to reassociate a couple of whiskerings, and ultimately allows us to apply the whisker..._selfEval_comp_eq lemmas
  repeat rw [whisker_exchange_assoc (vx.cone) (eComp _ _ _ _)]
  repeat rw [← e_assoc]
  repeat rw [associator_inv_naturality_left_assoc]
  repeat rw [associator_inv_naturality_middle_assoc]
  repeat rw [← comp_whiskerRight_assoc (vx.cone ▷ _)]
  rw [← comp_whiskerRight_assoc (v ◁ whiskerRight _ _ _), ← comp_whiskerRight_assoc (v ◁ whiskerLeft _ _ _)]
  repeat rw [← tensorHom_def'_assoc]
  rw [← Iso.inv_hom_id_assoc (β_ _ _) ((_ ⊗ₘ whiskerLeft _ _ _) ≫ _)]
  rw [cone_comp_whiskerRight_eq, cone_comp_whiskerLeft_eq]
  repeat rw [comp_whiskerRight_assoc]
  -- Reassociates the RHS again, which gives another α, and then on both sides: reassociate and reorder a couple of whiskerings to apply the whisker..._selfEval_comp_eq lemmas again
  rw [← e_assoc']
  repeat rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc _ (whiskerLeft _ _ _), whisker_exchange_assoc _ (whiskerRight _ _ _)]
  rw [associator_naturality_middle_assoc]
  rw [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp_assoc _ (vy.cone ▷ _)]
  rw [← whiskerLeft_comp_assoc _ (_ ◁ whiskerRight _ _ _)]
  repeat rw [← tensorHom_def'_assoc]
  dsimp [Functor.id_obj]
  rw [← Iso.inv_hom_id_assoc (β_ _ _) ((_ ⊗ₘ _) ≫ _)]
  rw [cone_comp_whiskerLeft_eq, cone_comp_whiskerRight_eq]
  repeat rw [whiskerLeft_comp_assoc]
  -- Combine an instance of α from the LHS and two instances of α and two whiskered instances of β from the RHS into β (v ⊗ Ehom) Ehom
  rw [Iso.inv_comp_eq]
  rw [← braiding_swap_eq_inv_braiding (Ehom V C x y) v]
  rw [← braiding_tensor_left_hom_assoc]
  -- Move β to the right place, which concludes the proof
  rw [braiding_inv_naturality_left_assoc]
  rw [← braiding_swap_eq_inv_braiding]

class TensoredCategory (V : Type u) [Category.{u₁} V] [MonoidalCategory V] [MonoidalClosed V]
    [SymmetricCategory V] (C : Type v) [EnrichedCategory V C] where
  tensor : (v : V) → (x : C) → Tensor v x

open TensoredCategory

/-- Tensoring, together with whiskering, constitutes a V-enriched functor `tensor_bifunc : V ⊗ C ⟶ C` --/
def tensor_bifunc [TensoredCategory V C] : EnrichedFunctor V (V ⊗[V] C) C :=
  enrichedTensor.eBifuncConstr V V C
    (fun v x ↦ (tensor v x).obj)
    (fun v w x ↦ whiskerRight V (tensor v x) (tensor w x))
    (fun v x y ↦ whiskerLeft V (tensor v x) (tensor v y))
    (fun v x ↦ whiskerRight_id V (tensor v x))
    (fun v x ↦ whiskerLeft_id V (tensor v x))
    (fun u v w x ↦ whiskerRight_comp V (tensor u x) (tensor v x) (tensor w x))
    (fun v x y z ↦ whiskerLeft_comp V (tensor v x) (tensor v y) (tensor v z))
    (fun v w x y ↦ whiskerRight_right_eq_whiskerLeft_left V (tensor v x) (tensor w x) (tensor v y) (tensor w y))

end Tensor

end Enriched

end CategoryTheory
