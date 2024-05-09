import Lean.Data.AssocList

open Lean (AssocList)

set_option autoImplicit false

universe u
universe v
variable {α : Type u}
variable [DecidableEq α]
variable {β : Type v}


def fun_upd : (α → Option β) → α → (Option β → β) → (α → Option β) :=
  fun f x k x' => if x' = x then some (k ((f x'))) else f x'

theorem fun_upd_eq (f : α → Option β) (x : α) (k : Option β → β) :
  (fun_upd f x k x) = some (k (f x)) := by
  simp [fun_upd]

theorem fun_upd_ne (f : α → Option β) (x₁ x₂ : α) (k : Option β → β) (h : x₂ ≠ x₁):
  (fun_upd f x₁ k x₂) = f x₂ := by
  simp [fun_upd, h]

theorem map_fun_upd_congr {β'}
    (f : α → Option β) (t : β → β') (x : α) (k : Option β → β) (k' : Option β' → β')
    (h : ∀ y?, t (k y?) = k' (y?.map t))
    : (fun x' => Option.map t (fun_upd f x k x')) = fun_upd (fun x' => Option.map t (f x')) x k' := by
  unfold fun_upd
  ext k' : 1
  split
  · simp [fun_upd, Option.map, h]
  · rfl

section Prefix

def commonPrefix : (xs ys : List α) → List α
  | _ , [] => []
  | [], _  => []
  | x::xs, y::ys =>
    if x = y then
      x :: commonPrefix xs ys
    else
      []

def hasPrefix : (xs ys : List α) → Bool
  | _ , [] => true
  | [], _ => false
  | x::xs, y::ys =>
    if x = y then
      hasPrefix xs ys
    else
      false

theorem commonPrefix_of_hasPrefix (xs ys : List α) (h : hasPrefix xs ys = true) :
    commonPrefix xs ys = ys := by
  induction xs, ys using commonPrefix.induct
  case case1 => simp [commonPrefix]
  case case2 => simp [hasPrefix] at h
  case case3 x xs ys => simp_all [commonPrefix, hasPrefix]
  case case4 x xs ys => simp_all [commonPrefix, hasPrefix]

end Prefix

namespace Trie.Abstract

/--
A very abstract idea of a trie data structure. We prove the relevant theorems about
their properties here, and show that more refined implementations behave like these.
-/
inductive Trie (α : Type u) (β : Type v) where
  | node (val : Option β) (c : α → Option (Trie α β)) : Trie α β

namespace Trie

def val : Trie α β → Option β | .node v _ => v
@[simp] theorem val_eq (v : Option β) (cs : α → Option (Trie α β)) : val (.node v cs) = v := by rfl

def c : Trie α β → (α → Option (Trie α β)) | .node _ c => c
@[simp] theorem c_eq (v : Option β) (cs : α → Option (Trie α β)) : c (.node v cs) = cs := by rfl

def empty : Trie α β := .node none (fun _ => .none)

def insert (t : Trie α β) : List α → β → Trie α β
  | [], v => .node (some v) t.c
  | k::ks, v => .node t.val <|
      fun_upd t.c k fun t => t.getD empty |>.insert ks v

def find? (t : Trie α β) : List α → Option β
  | [] => t.val
  | k::ks => match t.c k with
    | none => none
    | some t => t.find? ks

@[simp]
theorem find?_empty (k : List α) : (empty : Trie α β).find? k = none :=  by
  cases k <;> simp [empty, find?]

theorem find?_insert_eq (t : Trie α β) (k : List α) (v : β) :
    (t.insert k v).find? k = some v := by
  induction k generalizing t with
  | nil => simp [insert, find?, val]
  | cons k ks ih =>
    cases t with | _ v' c =>
    simpa [insert, find?, fun_upd] using ih _

theorem find?_insert_neq (t : Trie α β) (k k' : List α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  induction k generalizing t k' with
  | nil =>
    cases k' with | nil => contradiction | cons k' ks' =>
    cases t with | _ v' c =>
    simp [find?, insert]
  | cons k ks ih =>
    cases t with | _ v' c =>
    cases k' with
    | nil => simp [find?, insert]
    | cons k' ks' =>
      if hk : k' = k then
        subst k'
        have : ks ≠ ks' := by intro h; apply hne; cases h; rfl
        simp [insert, find?, hne, fun_upd, Option.getD, ih, this]
        cases c k <;> simp
      else
        simp [insert, find?, fun_upd, hk]


end Trie
end Trie.Abstract

namespace Lean.AssocList

/-! Missing definitions and lemmas about Lean.AssocList -/

def upsert (xs : AssocList α β) (k : α) (f : Option β → β) : AssocList α β :=
  match xs with
  | .cons k' v xs =>
    if k = k' then
      .cons k' (f (some v)) xs
    else
      .cons k' v (upsert xs k f)
  | .nil => .cons k (f none) .nil

theorem find?_upsert (xs : AssocList α β) (k1 k2 : α) (f : Option β → β) :
    (xs.upsert k1 f).find? k2 = fun_upd (xs.find? ·) k1 f k2 := by
  induction xs, k1, f using upsert.induct
  case case1 f k2 v xs =>
    simp [upsert, find?, fun_upd]
    split
    · simp_all
    · apply (if_neg (Ne.symm _)).symm
      simp_all
  case case2 k1 f k v xs hne ih =>
    simp [upsert, find?, hne, fun_upd]
    split
    next heq =>
      simp at heq; subst heq
      simp [if_neg (Ne.symm _), hne]
    next =>
      rw [ih]
      rfl
  case case3 k1 f =>
    simp [upsert, find?, fun_upd]
    split
    · simp_all
    · apply (if_neg (Ne.symm _)).symm
      simp_all


/-- Fused find and map with sizeOf information -/
def findSized? {γ} [SizeOf β] (xs : AssocList α β) (a : α) (f : (x : β) → (sizeOf x < sizeOf xs) → γ) :
    Option γ :=
  match xs with
  | nil         => none
  | cons k v es => match k == a with
    | true  => some (f v (by simp; omega))
    | false => findSized? es a (fun k _ => f k (by simp; omega))

@[simp]
def findSized?_eq_find?_map
  {γ} [SizeOf β] (xs : AssocList α β) (k : α) (f : (x : β) → γ) :
  findSized? xs k (fun y _ => f y) = (xs.find? k).map f := by
  induction xs <;> simp_all [findSized?, find?, Option.map]
  split <;> simp [*]

def mapSized {γ} [SizeOf β] (xs : AssocList α β) (f : (x : β) → (sizeOf x < sizeOf xs) → γ) :
    AssocList α γ :=
  match xs with
  | nil         => nil
  | cons k v es =>
    cons k (f v (by simp; omega)) (es.mapSized (fun k _ => f k (by simp; omega)))

@[simp]
def mapSized_eq_mapVal {γ} [SizeOf β] (xs : AssocList α β) (f : (x : β) → γ) :
    xs.mapSized (fun y _ => f y) = xs.mapVal f := by
  induction xs <;> simp_all [mapSized, mapVal]

theorem mapVal_upsert_congr {β'}
    (xs : AssocList α β)
    (t : β → β') (k : α) (f : Option β → β) (f' : Option β' → β')
    (h : ∀ y?, t (f y?) = f' (y?.map t))
    : (xs.upsert k f).mapVal t = (xs.mapVal t).upsert k f' := by
  induction xs
  · simp_all [upsert, mapVal]
  · simp only [upsert]
    split
    · simp_all [upsert, mapVal]
    · simp_all [upsert, mapVal]

@[simp] theorem find?_mapVal {β'} (xs : AssocList α β) (f : β → β') (k : α):
  (xs.mapVal f).find? k = (xs.find? k).map f := by
  induction xs
  · simp_all [find?, mapVal]
  · simp only [find?]
    split <;> simp_all


end Lean.AssocList

namespace Trie.AssocList

/-!
Refinement: Using associative lists instead of the abstract function
-/

inductive Trie (α : Type u) (β : Type v) where
  | node (val : Option β) (c : AssocList α (Trie α β)) : Trie α β

namespace Trie

def val : Trie α β → Option β | .node v _ => v
@[simp] theorem val_eq (v : Option β) (cs : AssocList α (Trie α β)) : val (.node v cs) = v := by rfl

def c : Trie α β → AssocList α (Trie α β) | .node _ c => c
@[simp] theorem c_eq (v : Option β) (cs : AssocList α (Trie α β)) : c (.node v cs) = cs := by rfl

def empty : Trie α β := .node none .empty

def insert (t : Trie α β) : List α → β → Trie α β
  | [], v => .node (some v) t.c
  | k::ks, v => .node t.val <|
      t.c.upsert k fun t => (t.getD empty).insert ks v

def find? (t : Trie α β) : List α → Option β
  | [] => t.val
  | k::ks => match t.c.find? k with
    | none => none
    | some t => t.find? ks

/-! We can relate these tries with the more abstract one -/

def abstract : Trie α β → Trie.Abstract.Trie α β
  | .node val? c => .node val? (fun k => c.findSized? k (fun t _ => t.abstract))
decreasing_by simp_wf; omega

@[simp]
theorem val_abstract (t : Trie α β) :
    t.abstract.val = t.val := by
  cases t; simp [Option.map, abstract]

theorem c_abstract (t : Trie α β) :
    t.abstract.c = (fun k => (t.c.find? k).map (·.abstract)) := by
  cases t
  simp [Option.map, abstract]

/-! Use this abstraction function to give specification for the operations -/

@[simp]
theorem empty_spec :
    (empty : Trie α β).abstract = .empty := by
  simp [abstract, empty, Trie.Abstract.Trie.empty]
  rfl

theorem find?_spec (t : Trie α β) (ks : List α):
    t.find? ks = t.abstract.find? ks := by
  induction t, ks using find?.induct
  case case1 t =>
    simp [find?, abstract, Trie.Abstract.Trie.find?]
  case case2 t k ks h =>
    simp [find?, Trie.Abstract.Trie.find?, h, c_abstract]
  case case3 t k ks h ih =>
    simpa only [find?, Trie.Abstract.Trie.find?, h, c_abstract] using ih

theorem insert_spec (t : Trie α β) (ks : List α) (v : β) :
    (insert t ks v).abstract = t.abstract.insert ks v := by
  induction t, ks, v using insert.induct
  case case1 t v =>
    simp [insert, abstract, Trie.Abstract.Trie.insert, c_abstract]
  case case2 t k ks ih =>
    simp [insert, abstract, Trie.Abstract.Trie.insert, c_abstract, AssocList.find?_upsert]
    apply map_fun_upd_congr
    intro t?
    rw [ih]; clear ih
    cases t? <;> simp

/-! And get the theory for free -/

theorem find?_empty (k : List α) : find? (empty : Trie α β) k = none := by
  simp [find?_spec, Trie.Abstract.Trie.find?_empty, empty_spec]

theorem find?_insert_eq (t : Trie α β) (k : List α) (v : β) :
    (t.insert k v).find? k = some v := by
  simpa [insert_spec, find?_spec] using Trie.Abstract.Trie.find?_insert_eq _ _ _

theorem find?_insert_neq (t : Trie α β) (k k' : List α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  simpa [insert_spec, find?_spec] using Trie.Abstract.Trie.find?_insert_neq _ _ _ hne _


/- A path is a trie where every node has one child -/

def path (val : Option β) (ps : List α) (t : Trie α β) : Trie α β :=
  match ps with
  | [] => t
  | p::ps => .node val (.cons p (path none ps t) .nil)

@[simp]
theorem path_val (ps : List α) (val : Option β) (h : ps ≠ []) (t : Trie α β):
  (path val ps t).val = val := by
  unfold path
  split; contradiction; simp

@[simp]
theorem path_c (p : α) (ps : List α) (val : Option β) (t : Trie α β):
  (path val (p::ps) t).c = .cons p (path none ps t) .nil := by
  simp [path]

@[simp]
theorem path_eq_insert (ks : List α) (v : β) :
   path none ks (node (some v) .nil) = empty.insert ks v := by
 induction ks <;>
    simp_all [path, AssocList.upsert, insert, empty]

theorem path_insert_eq_commonPrefix (ps ks : List α) (t : Trie α β) (v : β):
    (path none ps t).insert ks v =
      path none (commonPrefix ks ps)
        ((path none (List.drop (commonPrefix ks ps).length ps) t).insert
          (List.drop (commonPrefix ks ps).length ks) v) := by
  induction ks, ps using commonPrefix.induct
  · simp [path, commonPrefix, *]
  · simp [path, commonPrefix, *]
  · simp [path, commonPrefix, AssocList.Trie.insert, AssocList.upsert, *]
  · simp [path, commonPrefix, *]

theorem path_find_of_hasPrefix ps (t : AssocList.Trie α β) ks
    (h : hasPrefix ks ps = true) :
    (path none ps t).find? ks = t.find? (List.drop ps.length ks) := by
  induction ks generalizing ps
  · match ps with
    | [] => simp [path, find?]
    | _::_ => simp [hasPrefix] at h
  next k v ks ih =>
    match ps with
    | [] => simp [path, find?]
    | _::_ =>
      simp [hasPrefix] at h
      have ⟨h1, h2⟩ := h; clear h
      subst h1
      simp_all [path, find?, AssocList.find?]

theorem path_find_of_not_hasPrefix ps (t : Trie α β) ks
    (h : hasPrefix ks ps = false) :
    (path none ps t).find? ks = none := by
  induction ks generalizing ps
  · match ps with
    | [] => simp [hasPrefix] at h
    | _::_ => simp [path, find?]
  next k v ks ih =>
    match ps with
    | [] => simp [hasPrefix] at h
    | _::_ =>
      simp_all [path, AssocList.find?, find?]
      split <;> try rfl
      split at * <;> try contradiction
      simp_all
      subst_vars
      simp [hasPrefix] at h
      rw [ih _ h]

end Trie
end Trie.AssocList

namespace Trie.CompressedList

/--
Now adding path compression
-/

inductive Trie (α : Type u) (β : Type v) where
  | leaf (val : Option β)
  | path (val : Option β) (ps : List α) (hps : ps ≠ []) (t : Trie α β) : Trie α β
  | node (val : Option β) (c : AssocList α (Trie α β)) : Trie α β

namespace Trie

def empty : Trie α β := .leaf none

def mkPath (ps : List α) (t : Trie α β) : Trie α β :=
  if h : ps = [] then t else .path none ps h t

def insert (t : Trie α β) (ks : List α) (v : β) : Trie α β := match t with
  | .leaf val =>
    if h : ks = [] then
      .leaf (some v)
    else
      .path val ks h (.leaf (some v))
  | .path val ps hps t' =>
    if _h : ks = [] then
      .path (some v) ps hps t'
    else
      let pfx := commonPrefix ks ps
      if hpfx : pfx = [] then
        have c::ks' := ks
        have c'::ps' := ps
        let t := mkPath ks' (.leaf (some v))
        let t'' := mkPath ps' t'
        .node val (.cons c' t'' (.cons c t .nil)) -- order matters for refinement proof!
      else
          -- split common prefix, continue
          .path val pfx hpfx <| insert
            (.mkPath (ps.drop pfx.length) t')
            (ks.drop pfx.length)
            v
    | .node val cs =>
      match ks with
      | [] => .node (some v) cs
      | c::ks => .node val (cs.upsert c fun t? => (t?.getD empty).insert ks v)
termination_by ks.length
decreasing_by
· simp_wf
  rw [← List.length_eq_zero] at hpfx _h
  simp [pfx] at hpfx
  omega
· simp_wf

def find? : (t : Trie α β) → (ks : List α) → Option β
  | .leaf val, [] => val
  | .leaf _, (_::_) => none
  | .path val _ _ _, [] => val
  | .path _ ps _ t', ks@(_::_) =>
    if hasPrefix ks ps then
      t'.find? (ks.drop ps.length)
    else
      none
  | .node val _cs, [] => val
  | .node _val cs, k::ks =>
    match cs.find? k with
    | none => none
    | some t => t.find? ks
termination_by _ ks => ks.length
decreasing_by
· simp_wf
  subst_vars
  cases ps; contradiction;
  simp
  omega
· simp_wf


def uncompress : Trie α β → AssocList.Trie α β
  | .leaf val => .node val .nil
  | .node val cs => .node val (cs.mapSized fun t _ => t.uncompress)
  | .path val ps _ t => .path val ps t.uncompress

@[simp]
theorem uncompress_mkPath (ps : List α) (t : Trie α β) :
    (mkPath ps t).uncompress = .path none ps t.uncompress := by
  cases ps <;> simp [mkPath, AssocList.Trie.path, uncompress]


@[simp]
theorem empty_spec : (empty : Trie α β).uncompress = .empty := by rfl

theorem insert_spec (t : Trie α β) (ks : List α) (v : β) :
    (insert t ks v).uncompress = t.uncompress.insert ks v := by
  -- Bug in functional induction!
  -- induction t, ks, v using insert.induct
  unfold insert
  split
  next t val =>
    cases ks
    next =>
      simp [uncompress, AssocList.Trie.insert]
    next k ks =>
      simp [uncompress, AssocList.Trie.insert, AssocList.Trie.path, AssocList.upsert,
        AssocList.Trie.path_eq_insert]
  next ps _ t'=>
    match ks with
    | [] =>
      cases ps; contradiction
      simp [uncompress, AssocList.Trie.path, AssocList.Trie.insert]
    | (k::ks) =>
      have p::ps := ps
      simp only [↓reduceDite, ne_eq]
      match hpfx : commonPrefix (k::ks) (p::ps) with
      | [] =>
        simp only [↓reduceDite]
        simp [commonPrefix] at hpfx
        simp [uncompress, AssocList.Trie.path, AssocList.Trie.insert, AssocList.mapSized,
          AssocList.upsert, hpfx]
      | p1::ps =>
        simp [uncompress, AssocList.Trie.insert, AssocList.Trie.path]
        simp [commonPrefix] at hpfx
        split at hpfx <;> try contradiction
        simp at hpfx
        cases hpfx
        subst p k ps
        rw [insert_spec]
        simp [AssocList.upsert, uncompress]
        rw [← AssocList.Trie.path_insert_eq_commonPrefix]
  next t val cs =>
    match ks with
    | [] => simp [uncompress, AssocList.Trie.insert]
    | (k::ks) =>
      simp [uncompress, AssocList.Trie.insert]
      apply AssocList.mapVal_upsert_congr
      intro t?
      rw [insert_spec]
      match t? with
      | none => simp
      | some t' => simp
termination_by ks.length

theorem find?_spec (t : Trie α β) (ks : List α):
    t.uncompress.find? ks = t.find? ks := by
  induction t, ks using find?.induct
  all_goals solve
    | simp [uncompress, find?, AssocList.Trie.find?, AssocList.find?, *]
  next ps _ _ _ _ hpfx _ =>
    have p::ps := ps
    simp [hasPrefix] at hpfx
    cases hpfx with | _ heq hpfx =>
    subst p
    simp_all [uncompress, find?, AssocList.Trie.find?, AssocList.find?, hasPrefix,
      AssocList.Trie.path_find_of_hasPrefix]
  next ps _ _ _ _ hpfx =>
    have p::ps := ps
    simp_all [uncompress, find?, AssocList.Trie.find?, AssocList.find?, hasPrefix,
      AssocList.Trie.path_find_of_hasPrefix]
    split
    · simp
    next h =>
      split at h <;> simp at h
      subst h
      rw [AssocList.Trie.path_find_of_not_hasPrefix]
      apply hpfx
      simp_all

end Trie
end Trie.CompressedList


#exit

theorem Array.drop_data_cons {α : Type _} (as : Array α) (i : Nat) (h : i < as.size) :
  as.data.drop i = as[i] :: as.data.drop (i + 1) := by sorry

theorem Array.drop_data_nil {α : Type _} (as : Array α) (i : Nat) (h : ¬ i < as.size) :
  as.data.drop i = [] := by sorry

@[simp]
theorem Array.extract_data {α} (as : Array α) (i : Nat) (j : Nat) :
  (as.extract i j).data = (as.data.take j).drop i := by sorry

theorem Array.modify_data {α} (as : Array α) (i : Nat) (f : α → α) (h : i < as.size):
    (Array.modify as i f).data = as.data.take i ++ [f as[i]] ++ as.data.drop (i + 1) := by sorry

theorem Array.data_getElem {α} (as : Array α) (i : Nat) (h : i < as.size) :
  as.data[i] = as[i] := rfl

theorem Array.size_extract {α} (as : Array α) (start stop : Nat) :
    Array.size (Array.extract as start stop) = min stop (Array.size as) - start :=
  by sorry

theorem Array.get_extract {α} {i : Nat} {as : Array α} {start stop : Nat} (h : i < Array.size (Array.extract as start stop)) :
 (Array.extract as start stop)[i] = as[start + i]'(by simp [Array.size_extract] at *; omega) := sorry

def Array.attach {α} (as : Array α) : Array {x : α // x ∈ as} := by sorry


@[simp]
theorem Array.attach_singleton {α} (a : α) : #[a].attach = #[⟨a, .mk (by simp)⟩] := sorry

@[simp]
theorem Array.map_attach {α β} (xs : Array α) (f : α → β) :
  xs.attach.map (fun ⟨x, _⟩ => f x) = xs.map f := sorry

@[simp]
theorem Array.map_toArray {α β} (xs : List α) (f : α → β) :
  xs.toArray.map f = (xs.map f).toArray := sorry

@[simp]
theorem Array.map_two {α β} (x₁ x₂ : α) (f : α → β) :
  #[x₁, x₂].map f = #[f x₁, f x₂] := sorry

-- TODO: Lemma has wrong name in std
axiom Array.getElem_mem :
  ∀ {α : Type u} {i : Nat} (a : Array α) (h : i < Array.size a), a[i] ∈ a

namespace Trie.AbstractArray

/--
Like `Trie.Abstract.Trie`, but the operations (not the data structure) uses arrays for keys.
-/
abbrev Trie := @Trie.Abstract.Trie

namespace Trie

def empty := @Trie.Abstract.Trie.empty

def insert (t : Trie α β) (ks : Array α) (v : β) : Trie α β := go t 0
  where
  go t i := if h : i < ks.size then
    let k := ks[i]
    .node t.val (fun_upd empty t.c k fun t => go t (i + 1))
  else
    .node (some v) t.c
  termination_by ks.size - i

def find? (t : Trie α β) (ks : Array α) : Option β := go t 0
  where
  go t i := if h : i < ks.size then
    match t.c ks[i] with
    | none => none
    | some t => go t (i + 1)
  else
    t.val
  termination_by ks.size - i

/-
We first specify the operations on Arrays via their abstract counter-parts on lists.
-/

theorem insert_go_data (t : Trie α β) (ks : Array α) (v : β) (i : Nat) :
    insert.go ks v t i = Abstract.Trie.insert t (ks.data.drop i) v := by
  induction t, i using insert.go.induct (ks := ks) (v := v)
  case case1 t i hi IH =>
    unfold insert.go; simp only [hi, ↓reduceDite]
    simp [Abstract.Trie.insert, Array.drop_data_cons, empty, hi, IH]
  case case2 t i hi =>
    unfold insert.go; simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.insert, Array.drop_data_nil (h := hi)]

theorem insert_spec (t : Trie α β) (ks : Array α) (v : β) :
    insert t ks v = Abstract.Trie.insert t ks.data v := by simp [insert, insert_go_data]

theorem find?_go_data (t : Trie α β) (ks : Array α)  (i : Nat) :
    find?.go ks t i = Abstract.Trie.find? t (ks.data.drop i) := by
  induction t, i using find?.go.induct (ks := ks)
  case case1 t i hi IH =>
    unfold find?.go; simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.find?, Array.drop_data_cons, hi, IH]
  case case2 t i hi =>
    unfold find?.go; simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.find?, Array.drop_data_nil (h := hi)]

theorem find?_spec (t : Trie α β) (ks : Array α) :
    find? t ks = Abstract.Trie.find? t ks.data := by simp [find?, find?_go_data]

/-
Then the actual user-facing theorems follow quickly.
-/

theorem find?_empty (k : Array α) : find? (empty : Trie α β) k = none := by
  simp [find?_spec, Abstract.Trie.find?_empty, empty]

theorem find?_insert_eq (t : Trie α β) (k : Array α) (v : β) :
    (t.insert k v).find? k = some v := by
  simpa [insert_spec, find?_spec] using Abstract.Trie.find?_insert_eq _ _ _

theorem find?_insert_neq (t : Trie α β) (k k' : Array α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  have hne' : k.data ≠ k'.data := by intro h; apply hne; cases k; cases k'; simpa
  simpa [insert_spec, find?_spec] using Abstract.Trie.find?_insert_neq _ _ _ hne' _

end Trie

end Trie.AbstractArray


-- Helper functions for associative lists and arrays

namespace AssocList

def upsert (ks : List α) (vs : List β) (k : α) (f : Option β → β) : List α × List β :=
  match ks, vs with
  | k'::ks, v::vs =>
    if k = k' then
      (k'::ks, f (some v) :: vs)
    else
      let (ks, vs) := upsert ks vs k f
      (k'::ks, v::vs)
  | _, _ => ([k], [f none])

def find? (ks : List α) (vs : List β) (k : α) : Option β :=
  match ks, vs with
  | k'::ks, v::vs =>
    if k = k' then
      some v
    else
      find? ks vs k
  | _, _ => none

@[simp]
theorem find?_nil (vs : List β) (k : α) : find? [] vs k = none := by
  simp [find?]

theorem find?_upsert_eq (ks : List α) (vs : List β) (k : α) (f : Option β → β) :
    find? (upsert ks vs k f).1 (upsert ks vs k f).2 k = some (f (find? ks vs k)) := by
  induction ks generalizing vs with
  | nil => simp [upsert, find?]
  | cons k' ks ih =>
    cases vs with
    | nil => simp [upsert, find?]
    | cons v vs =>
      simp [upsert]
      split <;> simp [find?]
      next heq => subst k'; simp
      next hne => simp [hne]; apply ih

theorem find?_upsert_ne (ks : List α) (vs : List β) (k₁ k₂ : α) (f : Option β → β) (h : k₂ ≠ k₁) :
    find? (upsert ks vs k₁ f).1 (upsert ks vs k₁ f).2 k₂ = find? ks vs k₂ := by
  induction ks generalizing vs with
  | nil => simp [upsert, find?, h]
  | cons k' ks ih =>
    cases vs with
    | nil => simp [upsert, find?, h]
    | cons v vs =>
      simp [upsert]
      split <;> simp [find?]
      next heq => subst k'; simp [h]
      next hne => split <;> simp [*]

theorem upsert_1_congr {β₁ β₂} (ks : List α) (vs₁ : List β₁) (vs₂ : List β₂) (k : α)
  (f₁ : Option β₁ → β₁) (f₂ : Option β₂ → β₂) (h : vs₁.length = vs₂.length) :
  (upsert ks vs₁ k f₁).1 = (upsert ks vs₂ k f₂).1 := by
  induction ks generalizing vs₁ vs₂  with
  | nil => simp [upsert]
  | cons k' ks ih =>
    cases vs₁ with
    | nil =>
      cases vs₂ with
      | nil => simp [upsert]
      | cons => contradiction
    | cons =>
      cases vs₂ with
      | nil => contradiction
      | cons =>
        simp at h
        simp [upsert]
        split <;> simp
        apply ih _ _ h

theorem upsert_2_map {β₁ β₂} (ks : List α) (vs : List β₁) (f : β₁ → β₂) (k : α)
  (f₁ : Option β₁ → β₁) (f₂ : Option β₂ → β₂)
  (hf : ∀ x : Option β₁, f (f₁ x) = f₂ (x.map f)) :
  (upsert ks vs k f₁).2.map f = (upsert ks (vs.map f) k f₂).2 := by
  induction ks generalizing vs  with
  | nil => simp [upsert, hf]
  | cons k' ks ih =>
    cases vs with
    | nil => simp [upsert, hf]
    | cons =>
      simp [upsert]
      split <;> simp [hf]
      apply ih

end AssocList

namespace AssocArray

def upsert (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) : Array α × Array β :=
  go 0
  where
  go i :=
    if hi : i < ks.size then
      if hj : i < vs.size then
        if k = ks[i] then
          (ks, vs.modify i (fun v => f (some v)))
        else
          go (i + 1)
      else
        ((ks.extract 0 i).push k, vs.push (f none))
    else
      (ks.push k, (vs.extract 0 i).push (f none))
  termination_by ks.size - i

@[simp]
theorem upsert_nil (k : α) (f : Option β → β) : upsert #[] #[] k f = (#[k], #[f none]) := rfl

theorem upsert_singleton_ne (k₁ k₂ : α) (v₁ : β) (f : Option β → β) (hne : k₂ ≠ k₁):
  upsert #[k₁] #[v₁] k₂ f = (#[k₁, k₂], #[v₁, f none]) := by
  unfold upsert upsert.go
  simp [hne, Array.getElem_eq_data_get, List.get]
  rfl

def biDataDrop {α} {β} (pair : Array α × Array β) (i : Nat) : List α × List β :=
  (pair.1.data.drop i, pair.2.data.drop i)

theorem Array.data_ext {α} (a₁ a₂ : Array α) : (a₁ = a₂ ↔ a₁.data = a₂.data) := by
  constructor
  · intro h; subst h; rfl
  · intro h; cases a₁; cases a₂; simpa using h


def upsert_go_spec (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) (i : Nat) :
    upsert.go ks vs k f i =
      let (ks', vs') := AssocList.upsert (ks.data.drop i) (vs.data.drop i) k f;
      ((ks.data.take i ++ ks').toArray, (vs.data.take i ++ vs').toArray) := by
  induction i using upsert.go.induct (ks := ks) (vs := vs) (k := k) (f := f)
  case case1 i hi hj heq =>
    unfold upsert.go; simp only [hi, hj, heq, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, hj, ↓reduceIte,
      ↓reduceDite, Array.modify_data, hj]
    simp [← Array.data_getElem, List.get_drop_eq_drop ]
  case case2 i hi hj hneq IH =>
    unfold upsert.go; simp only [hi, hj, hneq, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, hj, hneq,
      ↓reduceIte, ↓reduceDite]
    rw [IH]
    simp [Array.data_ext, ← List.take_concat_get, hi, hj, Array.data_getElem]
  case case3 i hi hj =>
    have : vs.data.length ≤ i := by unfold Array.size at hj; omega
    unfold upsert.go; simp only [hi, hj, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, hj, ↓reduceIte, ↓reduceDite,
      List.take_length_le, List.drop_length_le, this]
  case case4 i hi =>
    have : ks.data.length ≤ i := by unfold Array.size at hi; omega
    unfold upsert.go; simp only [hi, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, ↓reduceIte, ↓reduceDite,
      List.take_length_le, List.drop_length_le, this]


def upsert_spec (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) :
    upsert ks vs k f =
      let (ks', vs') := AssocList.upsert ks.data vs.data k f;
      (ks'.toArray, vs'.toArray) := by simp [upsert, upsert_go_spec]

def find?' (ks : Array α) (vs : Array β) (k : α) : Option {x : β // x ∈ vs} := go 0
  where
  go i :=
    if hi : i < ks.size then
      if hj : i < vs.size then
        if k = ks[i] then
          some ⟨vs[i], Array.getElem_mem _ hj⟩
        else
          go (i + 1)
      else
        none
    else
      none
  termination_by ks.size - i

def find? (ks : Array α) (vs : Array β) (k : α) : Option β := (find?' ks vs k).map (·.val)

def find?'_go_spec (ks : Array α) (vs : Array β) (k : α) (i : Nat) :
    (find?'.go ks vs k i).map (·.val) = AssocList.find? (ks.data.drop i) (vs.data.drop i) k := by
  induction i using find?'.go.induct (ks := ks) (vs := vs) (k := k)
  case case1 i hi hj heq =>
    unfold find?'.go; simp only [hi, hj, heq, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, hj, heq, ↓reduceIte, ↓reduceDite]
  case case2 i hi hj hneq IH =>
    unfold find?'.go; simp only [hi, hj, hneq, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, hj, hneq,
      ↓reduceIte, ↓reduceDite, IH]
  case case3 i hi hj =>
    have : vs.data.length ≤ i := by unfold Array.size at hj; omega
    unfold find?'.go; simp only [hi, hj, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, hj, ↓reduceIte, ↓reduceDite,
      List.drop_length_le, this, Option.map_none']
  case case4 i hi =>
    have : ks.data.length ≤ i := by unfold Array.size at hi; omega
    unfold find?'.go; simp only [hi, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, ↓reduceIte, ↓reduceDite,
      List.drop_length_le, this, Option.map_none']

def find?'_spec (ks : Array α) (vs : Array β) (k : α) :
    (find?' ks vs k).map (·.val) = AssocList.find? ks.data vs.data k :=
  by simp [find?', find?'_go_spec]

def find?_spec (ks : Array α) (vs : Array β) (k : α) :
    find? ks vs k = AssocList.find? ks.data vs.data k := find?'_spec _ _ _

@[simp]
theorem find?_nil (vs : Array β) (k : α) : find? #[] vs k = none := by
  simp [find?_spec]

theorem find?_upsert_eq (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) :
    find? (upsert ks vs k f).1 (upsert ks vs k f).2 k = some (f (find? ks vs k)) := by
  simp [upsert_spec, find?_spec]
  apply AssocList.find?_upsert_eq

theorem find?_upsert_ne (ks : Array α) (vs : Array β) (k₁ k₂ : α) (f : Option β → β)  (h : k₂ ≠ k₁) :
    find? (upsert ks vs k₁ f).1 (upsert ks vs k₁ f).2 k₂ = find? ks vs k₂:= by
  simp [upsert_spec, find?_spec]
  apply AssocList.find?_upsert_ne (h := h)

theorem upsert_1_congr {β₁ β₂} (ks : Array α) (vs₁ : Array β₁) (vs₂ : Array β₂) (k : α)
  (f₁ : Option β₁ → β₁) (f₂ : Option β₂ → β₂) (h : vs₁.size = vs₂.size) :
  (upsert ks vs₁ k f₁).1 = (upsert ks vs₂ k f₂).1 := by
  simp [upsert_spec]
  apply AssocList.upsert_1_congr
  apply h

theorem upsert_2_map {β₁ β₂} (ks : Array α) (vs : Array β₁) (f : β₁ → β₂) (k : α)
  (f₁ : Option β₁ → β₁) (f₂ : Option β₂ → β₂)
  (hf : ∀ x : Option β₁, f (f₁ x) = f₂ (x.map f)) :
  (upsert ks vs k f₁).2.map f = (upsert ks (vs.map f) k f₂).2 := by
  simp [upsert_spec]
  apply AssocList.upsert_2_map
  apply hf

end AssocArray

namespace Trie.Array

/--
A more realistic implementation, using Arrays instead of functions.
-/
inductive Trie (α : Type u) (β : Type v) where
  | node (val : Option β) (ks : Array α) (vs : Array (Trie α β)) : Trie α β

namespace Trie

def empty : Trie α β := .node none #[] #[]

def insert (t : Trie α β) (ks : Array α) (v : β) : Trie α β := go t 0 where
  go | .node val ks' vs, i =>
      if h : i < ks.size then
        let (ks'', vs'') := AssocArray.upsert ks' vs ks[i] fun t? =>
          go (t?.getD empty) (i + 1)
        .node val ks'' vs''
      else
        .node (some v) ks' vs
  termination_by _ i => ks.size - i

def find? (t : Trie α β) (ks : Array α) : Option β := go t 0 where
  go | .node val ks' vs, i =>
      if h : i < ks.size then
        match AssocArray.find? ks' vs ks[i] with
        | none => none
        | some t => go t (i + 1)
      else
        val
  termination_by _ i => ks.size - i

def toAbstractArray : Trie α β → AbstractArray.Trie α β
  | .node val ks vs => .node val fun k =>
    match AssocArray.find?' ks vs k with
    | none => none
    | some ⟨t, _⟩ => some t.toAbstractArray
termination_by t => sizeOf t

def toAbstractArray_eq (val : Option β) (ks : Array α) (vs : Array (Trie α β)) :
  toAbstractArray (Trie.node val ks vs) = .node val fun k =>
    match AssocArray.find? ks vs k with
    | none => none
    | some t => some t.toAbstractArray := by
  conv => left; unfold toAbstractArray
  congr 1
  funext k
  unfold AssocArray.find?
  simp [Option.map]
  split <;> simp [*]


@[simp]
theorem empty_spec :
    (empty : Trie α β).toAbstractArray = AbstractArray.Trie.empty := by
  simp [toAbstractArray, empty, AbstractArray.Trie.empty]
  rfl

theorem find?_go_spec (t : Trie α β) (ks : Array α) (i : Nat) :
    find?.go ks t i = AbstractArray.Trie.find?.go ks t.toAbstractArray i := by
  induction t, i using find?.go.induct (ks := ks)
  case case1 v ks' vs i hi IH =>
    unfold find?.go
    unfold AbstractArray.Trie.find?.go
    simp only [hi, ↓reduceDite]
    simp only [toAbstractArray_eq, Option.getD, Abstract.Trie.c, IH]
  case case2 v ks' vs i hi t hfind IH =>
    unfold find?.go
    unfold AbstractArray.Trie.find?.go
    simp only [hi, ↓reduceDite]
    simp only [toAbstractArray_eq, Option.getD, Abstract.Trie.c, IH, hfind]
  case case3 val v val' i hi =>
    unfold find?.go
    unfold AbstractArray.Trie.find?.go
    simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.val, toAbstractArray_eq]

theorem find?_spec (t : Trie α β) (ks : Array α):
    t.find? ks = t.toAbstractArray.find? ks := by
  simp [find?, AbstractArray.Trie.find?, find?_go_spec]

theorem insert_go_spec (t : Trie α β) (ks : Array α) (i : Nat) (v : β):
    (insert.go ks v t i).toAbstractArray  = AbstractArray.Trie.insert.go ks v t.toAbstractArray i := by
  induction t, i using insert.go.induct (ks := ks) (v := v)
  case case1 val ks' vs i hi ks'' vs'' hfind IH =>
    unfold insert.go AbstractArray.Trie.insert.go
    simp only [hi, ↓reduceDite]
    simp only [toAbstractArray_eq, Abstract.Trie.c]
    -- this is ugly:
    have := (Prod.eta _).trans hfind
    simp at this; cases this
    subst ks'' vs''
    clear hfind

    congr 1
    funext k
    if h : k = ks[i] then
      simp only [↓reduceIte, h]
      simp only [AssocArray.find?_upsert_eq, fun_upd_eq]
      rw [IH]
      simp [Option.getD]
      split <;> simp [*]
    else
      simp only [↓reduceIte, h, AssocArray.find?_upsert_ne (h := h), fun_upd_ne (h := h)]
  case case2 v ks' vs i hi =>
    unfold insert.go
    unfold AbstractArray.Trie.insert.go
    simp only [hi, ↓reduceDite]
    simp only [toAbstractArray, Abstract.Trie.c]

theorem insert_spec (t : Trie α β) (ks : Array α) (v : β):
    (insert t ks v).toAbstractArray  = AbstractArray.Trie.insert t.toAbstractArray ks v :=
  insert_go_spec ..


theorem find?_empty (k : Array α) : find? (empty : Trie α β) k = none := by
  simp [find?_spec, AbstractArray.Trie.find?_empty]

theorem find?_insert_eq (t : Trie α β) (k : Array α) (v : β) :
    (t.insert k v).find? k = some v := by
  simp [insert_spec, find?_spec]
  apply AbstractArray.Trie.find?_insert_eq

theorem find?_insert_neq (t : Trie α β) (k k' : Array α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  simpa [insert_spec, find?_spec] using AbstractArray.Trie.find?_insert_neq _ _ _ hne _

end Trie

end Trie.Array

namespace Trie.Compressed

/--
Now additing path compression.
-/
inductive Trie (α : Type u) (β : Type v) where
  | leaf (val : Option β)
  | path (val : Option β) (ps : Array α) (hps : 0 < ps.size) (t : Trie α β) : Trie α β
  | node (val : Option β) (ks : Array α) (vs : Array (Trie α β)) : Trie α β

namespace Trie

def empty : Trie α β := .leaf none

def commonPrefix (xs : Array α) (ys : Array α) (offset1 : Nat) : Nat :=
  let rec loop (i : Nat) : Nat :=
    if h : offset1 + i < xs.size then
      if h' : i < ys.size then
        if xs[offset1 + i] = ys[i] then
          loop (i + 1)
        else
          i
      else
        i
    else
      i
    termination_by ys.size - i
  loop 0

def hasPrefix (xs : Array α) (ys : Array α) (offset1 : Nat) : Bool :=
  let rec loop (i : Nat) : Bool :=
    if h' : i < ys.size then
      if h : offset1 + i < xs.size then
        if xs[offset1 + i] = ys[i] then
          loop (i + 1)
        else
          false
      else
        false
    else
      true
    termination_by ys.size - i
  loop 0

theorem commonPrefix_loop_of_hasPrefix_loop (xs : Array α) (ys : Array α) (offset1 i : Nat)
    (hi : i ≤ ys.size) (h : hasPrefix.loop xs ys offset1 i = true) :
    commonPrefix.loop xs ys offset1 i = ys.size := by
  induction i using hasPrefix.loop.induct (xs := xs) (ys := ys) (offset1 := offset1)
  case case1 IH =>
    unfold hasPrefix.loop at h; simp [*] at h
    unfold commonPrefix.loop; simp [*]
    apply IH _ h
    omega
  case case2 | case3 => unfold hasPrefix.loop at h; simp [*] at h
  case case4 i hi =>
    unfold commonPrefix.loop; simp [*]
    omega

theorem commonPrefix_of_hasPrefix (xs : Array α) (ys : Array α) (offset1 : Nat)
    (h : hasPrefix xs ys offset1 = true) :
    commonPrefix xs ys offset1 = ys.size :=
  commonPrefix_loop_of_hasPrefix_loop xs ys offset1 0 (Nat.zero_le _) h

def mkPath (ps : Array α) (t : Trie α β) : Trie α β :=
  if h : 0 < ps.size  then .path none ps h t else t

def insert (t : Trie α β) (ks : Array α) (v : β) : Trie α β := go 0 t where
  go (i : Nat)
    | .leaf val =>
      if h : i < ks.size then
        path val (ks.extract i ks.size) (by simp [Array.size_extract]; omega) (.leaf (some v))
      else
        .leaf (some v)
    | .path val ps hps t' =>
      if h : i < ks.size then
        let j := commonPrefix ks ps i
        if hj : 0 < j then
          -- split common prefix, continue
          .path val (ps.extract 0 j) (by simp [Array.size_extract];omega) <| go (i + j) <|
              .mkPath (ps.extract j ps.size) t'
        else
          -- no common prefix, split off first key
          let c := ks[i]
          let c' := ps[0]'(by omega)
          let t := mkPath (ks.extract (i+1) ks.size) (.leaf (some v))
          let t'' := mkPath (ps.extract 1 ps.size) t'
          .node val #[c', c] #[t'', t] -- order matters for refinemnet proof!
      else
        .path (some v) ps hps t'
    | .node val ks' vs =>
      if h : i < ks.size then
        let (ks'', vs'') := AssocArray.upsert ks' vs ks[i] fun t? =>
          go (i + 1) (t?.getD empty)
        .node val ks'' vs''
      else
        .node (some v) ks' vs
  termination_by ks.size - i
  decreasing_by all_goals simp_wf; omega

def find? (t : Trie α β) (ks : Array α) : Option β := go 0 t where
  go
    | i, .leaf val =>
      if i < ks.size then
        none
      else
        val
    | i, path val ps _ t' =>
      if i < ks.size then
        if hasPrefix ks ps i then
          go (i + ps.size) t'
        else
          none
      else
        val
    | i, .node val ks' vs =>
      if h : i < ks.size then
        match AssocArray.find? ks' vs ks[i] with
        | none => none
        | some t => go (i + 1) t
      else
        val
  termination_by i => ks.size - i
  decreasing_by all_goals simp_wf; omega

def uncompressPath (val : Option β) (ps : Array α) (i : Nat) (t : Array.Trie α β) : Array.Trie α β :=
  if h : i < ps.size then
    .node val #[ps[i]] #[uncompressPath none ps (i + 1) t]
  else
    t
termination_by ps.size - i

noncomputable
def uncompress : Trie α β → Array.Trie α β
  | .leaf val => .node val #[] #[]
  | .node val ks vs => .node val ks (vs.attach.map fun ⟨t, _⟩ => t.uncompress)
  | .path val ps _ t => uncompressPath val ps 0 (t.uncompress)
termination_by t => sizeOf t

@[simp]
theorem empty_spec : (empty : Trie α β).uncompress = .empty := by rfl

@[simp]
theorem path_extract (val : Option β) (ks : Array α) (i j : Nat) t :
  uncompressPath val (Array.extract ks i (Array.size ks)) j t =
  uncompressPath val ks (i + j) t := by
  unfold uncompressPath;
  simp [Array.size_extract, Array.get_extract]
  split
  next hj =>
    have : i + j < Array.size ks := by omega
    simp [this, path_extract (ks := ks) (j := j+1)]
    rfl
  next hj =>
    have : ¬ (i + j < Array.size ks) := by omega
    simp [this]
termination_by ks.size - j
decreasing_by simp_wf; omega

@[simp]
theorem uncompress_mkPath (ps : Array α) (t : Trie α β):
    uncompress (mkPath ps t) = uncompressPath none ps 0 t.uncompress := by
  unfold mkPath
  split
  next hps => simp [uncompress]
  next hps => unfold uncompressPath; simp [hps]

theorem path_node_eq_insert
  (val : Option β) (ks : Array α) (i : Nat) (v : β) :
  uncompressPath val ks i (Array.Trie.node (some v) #[] #[]) =
  Array.Trie.insert.go ks v (Array.Trie.node val #[] #[]) i := by sorry


theorem insert_go_spec (t : Trie α β) (ks : Array α) (i : Nat) (v : β):
    (insert.go ks v i t).uncompress  = .insert.go ks v t.uncompress i := by
  cases t with
  | leaf val =>
    simp [insert.go, *, uncompress]
    split
    next hi =>
      simp [uncompress]
      exact path_node_eq_insert ..
    next hi0 =>
      simp [insert.go, *, uncompress, Array.Trie.insert.go]
  | path val ps hps t' =>
    simp [insert.go, *, uncompress]
    split
    next hi =>
      split
      next hcommonPrefix_pos =>
        simp [uncompress]
        rw [insert_go_spec]
        simp
        sorry -- insert into uncompressPath goes past common prefix
      next hcommonPrefix_0 =>
        have : commonPrefix ks ps i = 0 := by omega
        have hne : ks[i] ≠ ps[0] := by sorry
        simp [uncompress, this, Array.Trie.insert.go, hi]
        conv => right; unfold uncompressPath
        simp [hps, Array.Trie.insert.go, hi, AssocArray.upsert_singleton_ne (hne := hne)]
        sorry -- insert into empty is uncompressPath
    next hi0 =>
      simp [insert.go, *, uncompress, Array.Trie.insert.go]
      unfold uncompressPath
      simp [hps, Array.Trie.insert.go, hi0]
  | node val ks' cs =>
    simp [insert.go]
    split
    next hi =>
      simp [uncompress, Array.Trie.insert.go, hi]
      constructor
      · apply AssocArray.upsert_1_congr
        simp
      · apply AssocArray.upsert_2_map
        intro x
        rw [insert_go_spec]
        cases x <;> rfl
    next hi0 =>
      simp [insert.go, *, uncompress, Array.Trie.insert.go]
termination_by ks.size - i
decreasing_by all_goals simp_wf; omega
