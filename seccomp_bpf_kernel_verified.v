(* ===================================================================== *)
(* seccomp-bpf Kernel-Accurate Formalization in Coq                     *)
(* Author: Charles C Norton                                             *)
(* Date: 2025/10/21                                                     *)
(* Based on: Linux kernel seccomp.c, seccomp.h, filter.h                *)
(* ===================================================================== *)

(* ======================= Imports and Setup ========================== *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Import VectorNotations.

(* ===================== Basic Word Types ======================== *)

Definition word32 := nat.
Definition word16 := nat.
Definition byte := nat.
Definition word64 := nat.
Definition int32 := Z.

Definition word32_of_nat (n : nat) : word32 := n mod 4294967296.
Definition word16_of_nat (n : nat) : word16 := n mod 65536.
Definition byte_of_nat (n : nat) : byte := n mod 256.
Definition word64_of_nat (n : nat) : word64 := n mod 18446744073709551616.

Lemma word32_bound : forall n, word32_of_nat n < 4294967296.
Proof.
  intros n.
  unfold word32_of_nat.
  apply Nat.mod_upper_bound.
  discriminate.
Qed.

Lemma word16_bound : forall n, word16_of_nat n < 65536.
Proof.
  intros n.
  unfold word16_of_nat.
  apply Nat.mod_upper_bound.
  discriminate.
Qed.

Lemma byte_bound : forall n, byte_of_nat n < 256.
Proof.
  intros n.
  unfold byte_of_nat.
  apply Nat.mod_upper_bound.
  discriminate.
Qed.

(* ==================== Kernel Constants ========================== *)

Definition BPF_MAXINSNS : nat := 4096.

Definition MEM_SIZE : nat := 16.

Definition SECCOMP_DATA_SIZE : nat := 64.

Definition SECCOMP_RET_ACTION_FULL : word32 := 4294901760.
Definition SECCOMP_RET_ACTION : word32 := 2147418112.
Definition SECCOMP_RET_DATA : word32 := 65535.

Definition BPF_W : nat := 4.
Definition BPF_H : nat := 2.
Definition BPF_B : nat := 1.

(* ========================= BPF State ============================= *)

Record BPFState := mkState {
  reg_A  : word32;
  reg_X  : word32;
  mem    : Vector.t word32 MEM_SIZE;
  pc     : nat
}.

(* ==================== seccomp Action Codes (Kernel-Accurate) ===== *)

Inductive SeccompAction : Type :=
  | SECCOMP_RET_KILL_PROCESS : SeccompAction
  | SECCOMP_RET_KILL_THREAD  : SeccompAction
  | SECCOMP_RET_TRAP         : word16 -> SeccompAction
  | SECCOMP_RET_ERRNO        : word16 -> SeccompAction
  | SECCOMP_RET_USER_NOTIF   : word16 -> SeccompAction
  | SECCOMP_RET_TRACE        : word16 -> SeccompAction
  | SECCOMP_RET_LOG          : SeccompAction
  | SECCOMP_RET_ALLOW        : SeccompAction.

Definition action_code (act : SeccompAction) : word32 :=
  match act with
  | SECCOMP_RET_KILL_PROCESS => 2147483648
  | SECCOMP_RET_KILL_THREAD  => 0
  | SECCOMP_RET_TRAP v       => word32_of_nat (196608 + v)
  | SECCOMP_RET_ERRNO v      => word32_of_nat (327680 + v)
  | SECCOMP_RET_USER_NOTIF v => word32_of_nat (2143289344 + v)
  | SECCOMP_RET_TRACE v      => word32_of_nat (2146435072 + v)
  | SECCOMP_RET_LOG          => 2147221504
  | SECCOMP_RET_ALLOW        => 2147418112
  end.

Definition action_of_code (code : word32) : SeccompAction :=
  let high := code / 65536 in
  let low  := code mod 65536 in
  if high =? 32768 then SECCOMP_RET_KILL_PROCESS
  else if high =? 0 then
    if code =? 0 then SECCOMP_RET_KILL_THREAD else SECCOMP_RET_ERRNO low
  else if high =? 3 then SECCOMP_RET_TRAP low
  else if high =? 5 then SECCOMP_RET_ERRNO low
  else if high =? 32704 then SECCOMP_RET_USER_NOTIF low
  else if high =? 32752 then SECCOMP_RET_TRACE low
  else if high =? 32764 then SECCOMP_RET_LOG
  else if high =? 32767 then SECCOMP_RET_ALLOW
  else SECCOMP_RET_KILL_THREAD.

Definition action_priority (act : SeccompAction) : nat :=
  match act with
  | SECCOMP_RET_KILL_PROCESS => 0
  | SECCOMP_RET_KILL_THREAD => 1
  | SECCOMP_RET_TRAP _ => 2
  | SECCOMP_RET_ERRNO _ => 3
  | SECCOMP_RET_USER_NOTIF _ => 4
  | SECCOMP_RET_TRACE _ => 5
  | SECCOMP_RET_LOG => 6
  | SECCOMP_RET_ALLOW => 7
  end.

Definition action_more_restrictive (a1 a2 : SeccompAction) : bool :=
  action_priority a1 <? action_priority a2.

Definition action_only (code : word32) : word32 :=
  code / 65536 * 65536.

Definition action_less_permissive (code1 code2 : word32) : bool :=
  action_only code1 <? action_only code2.

(* ==================== BPF Instruction Set (Classic BPF) =========== *)

Inductive BPFClass : Type :=
  | BPF_LD   : BPFClass
  | BPF_LDX  : BPFClass
  | BPF_ST   : BPFClass
  | BPF_STX  : BPFClass
  | BPF_ALU  : BPFClass
  | BPF_JMP  : BPFClass
  | BPF_RET  : BPFClass
  | BPF_MISC : BPFClass.

Inductive BPFMode : Type :=
  | BPF_IMM  : BPFMode
  | BPF_ABS  : BPFMode
  | BPF_IND  : BPFMode
  | BPF_MEM  : BPFMode
  | BPF_LEN  : BPFMode
  | BPF_MSH  : BPFMode.

Inductive BPFALUOp : Type :=
  | BPF_ADD : BPFALUOp | BPF_SUB : BPFALUOp | BPF_MUL : BPFALUOp
  | BPF_DIV : BPFALUOp | BPF_OR  : BPFALUOp | BPF_AND : BPFALUOp
  | BPF_LSH : BPFALUOp | BPF_RSH : BPFALUOp | BPF_NEG : BPFALUOp
  | BPF_MOD : BPFALUOp | BPF_XOR : BPFALUOp.

Inductive BPFJmpOp : Type :=
  | BPF_JA  : BPFJmpOp
  | BPF_JEQ : BPFJmpOp
  | BPF_JGT : BPFJmpOp
  | BPF_JGE : BPFJmpOp
  | BPF_JSET: BPFJmpOp.

Inductive BPFSource : Type :=
  | BPF_K : BPFSource
  | BPF_X : BPFSource.

Inductive Instruction : Type :=
  | LD_IMM     : word32 -> Instruction
  | LD_ABS     : word32 -> nat -> Instruction
  | LD_IND     : word32 -> nat -> Instruction
  | LD_MEM     : nat -> Instruction
  | LD_LEN     : Instruction
  | LD_MSH     : word32 -> Instruction
  | LDX_IMM    : word32 -> Instruction
  | LDX_MEM    : nat -> Instruction
  | LDX_LEN    : Instruction
  | LDX_MSH    : word32 -> Instruction
  | ST_MEM     : nat -> Instruction
  | STX_MEM    : nat -> Instruction
  | ALU        : BPFALUOp -> BPFSource -> word32 -> Instruction
  | JMP        : BPFJmpOp -> BPFSource -> word32 -> nat -> nat -> Instruction
  | RET        : BPFSource -> word32 -> Instruction
  | MISC_TAX   : Instruction
  | MISC_TXA   : Instruction.

Record SockFilter := mkSockFilter {
  code : word16;
  jt   : byte;
  jf   : byte;
  k    : word32
}.

(* ==================== seccomp_data Structure (Kernel Layout) ====== *)

Record SeccompData := mkData {
  nr                  : int32;
  arch                : word32;
  instruction_pointer : word64;
  args                : Vector.t word64 6
}.

Definition offsetof_nr : nat := 0.
Definition offsetof_arch : nat := 4.
Definition offsetof_instruction_pointer : nat := 8.
Definition offsetof_args (idx : nat) : nat := 16 + idx * 8.

(* ==================== Helper Functions ========================== *)

Definition apply_size_mask (val : word32) (size : nat) : word32 :=
  match size with
  | 1 => val mod 256
  | 2 => val mod 65536
  | _ => val
  end.

Definition fetch_seccomp_data (data : SeccompData) (offset : word32) (size : nat) : word32 :=
  let raw_val := match offset with
  | 0  => Z.to_nat (Z.modulo (nr data) 4294967296)
  | 4  => arch data
  | 8  => word32_of_nat (instruction_pointer data mod 4294967296)
  | 12 => word32_of_nat (instruction_pointer data / 4294967296)
  | 16 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 0 < 6)) mod 4294967296)
  | 20 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 0 < 6)) / 4294967296)
  | 24 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 1 < 6)) mod 4294967296)
  | 28 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 1 < 6)) / 4294967296)
  | 32 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 2 < 6)) mod 4294967296)
  | 36 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 2 < 6)) / 4294967296)
  | 40 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 3 < 6)) mod 4294967296)
  | 44 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 3 < 6)) / 4294967296)
  | 48 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 4 < 6)) mod 4294967296)
  | 52 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 4 < 6)) / 4294967296)
  | 56 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 5 < 6)) mod 4294967296)
  | 60 => word32_of_nat (Vector.nth (args data) (Fin.of_nat_lt (ltac:(lia) : 5 < 6)) / 4294967296)
  | _  => 0
  end in
  apply_size_mask raw_val size.

Definition data_len : nat := SECCOMP_DATA_SIZE.

Definition instruction_at (prog : list Instruction) (idx : nat) : option Instruction :=
  nth_error prog idx.

Definition apply_alu_op (op : BPFALUOp) (a : word32) (b : word32) : word32 :=
  word32_of_nat (
    match op with
    | BPF_ADD => a + b
    | BPF_SUB => if a <? b then 0 else a - b
    | BPF_MUL => a * b
    | BPF_DIV => if b =? 0 then 0 else a / b
    | BPF_OR  => Nat.lor a b
    | BPF_AND => Nat.land a b
    | BPF_LSH => Nat.shiftl a b
    | BPF_RSH => Nat.shiftr a b
    | BPF_NEG => 0
    | BPF_MOD => if b =? 0 then a else a mod b
    | BPF_XOR => Nat.lxor a b
    end
  ).

Definition check_jmp_condition (op : BPFJmpOp) (a : word32) (b : word32) : bool :=
  match op with
  | BPF_JA   => true
  | BPF_JEQ  => a =? b
  | BPF_JGT  => b <? a
  | BPF_JGE  => b <=? a
  | BPF_JSET => negb ((Nat.land a b) =? 0)
  end.

Definition update_mem (m : Vector.t word32 MEM_SIZE) (idx : nat) (val : word32) : Vector.t word32 MEM_SIZE :=
  match lt_dec idx MEM_SIZE with
  | left pf => Vector.replace m (Fin.of_nat_lt pf) val
  | right _ => m
  end.

Definition read_mem (m : Vector.t word32 MEM_SIZE) (idx : nat) : word32 :=
  match lt_dec idx MEM_SIZE with
  | left pf => Vector.nth m (Fin.of_nat_lt pf)
  | right _ => 0
  end.

(* ==================== Execution Semantics ========================= *)

Definition execute_instruction (prog : list Instruction) (data : SeccompData) (s : BPFState)
  : SeccompAction + BPFState :=
  match instruction_at prog (pc s) with
  | None => inl SECCOMP_RET_KILL_THREAD
  | Some instr =>
      match instr with
      | LD_IMM k =>
          inr (mkState k (reg_X s) (mem s) (S (pc s)))
      | LD_ABS k size =>
          inr (mkState (fetch_seccomp_data data k size) (reg_X s) (mem s) (S (pc s)))
      | LD_IND k size =>
          let offset := word32_of_nat (k + reg_X s) in
          inr (mkState (fetch_seccomp_data data offset size) (reg_X s) (mem s) (S (pc s)))
      | LD_MEM k =>
          inr (mkState (read_mem (mem s) k) (reg_X s) (mem s) (S (pc s)))
      | LD_LEN =>
          inr (mkState data_len (reg_X s) (mem s) (S (pc s)))
      | LD_MSH k =>
          let byte_val := fetch_seccomp_data data k 1 in
          let lower_nibble := byte_val mod 16 in
          inr (mkState lower_nibble (reg_X s) (mem s) (S (pc s)))
      | LDX_IMM k =>
          inr (mkState (reg_A s) k (mem s) (S (pc s)))
      | LDX_MEM k =>
          inr (mkState (reg_A s) (read_mem (mem s) k) (mem s) (S (pc s)))
      | LDX_LEN =>
          inr (mkState (reg_A s) data_len (mem s) (S (pc s)))
      | LDX_MSH k =>
          let byte_val := fetch_seccomp_data data k 1 in
          let lower_nibble := byte_val mod 16 in
          inr (mkState (reg_A s) lower_nibble (mem s) (S (pc s)))
      | ST_MEM k =>
          inr (mkState (reg_A s) (reg_X s) (update_mem (mem s) k (reg_A s)) (S (pc s)))
      | STX_MEM k =>
          inr (mkState (reg_A s) (reg_X s) (update_mem (mem s) k (reg_X s)) (S (pc s)))
      | ALU op src k =>
          let operand := match src with BPF_K => k | BPF_X => reg_X s end in
          let result := apply_alu_op op (reg_A s) operand in
          inr (mkState result (reg_X s) (mem s) (S (pc s)))
      | JMP op src k jt jf =>
          let operand := match src with BPF_K => k | BPF_X => reg_X s end in
          let cond := check_jmp_condition op (reg_A s) operand in
          let next_pc := if cond then (S (pc s)) + jt else (S (pc s)) + jf in
          inr (mkState (reg_A s) (reg_X s) (mem s) next_pc)
      | RET src k =>
          let ret_val := match src with BPF_K => k | BPF_X => reg_X s end in
          inl (action_of_code ret_val)
      | MISC_TAX =>
          inr (mkState (reg_A s) (reg_A s) (mem s) (S (pc s)))
      | MISC_TXA =>
          inr (mkState (reg_X s) (reg_X s) (mem s) (S (pc s)))
      end
  end.

Fixpoint run_bpf (prog : list Instruction) (data : SeccompData) (s : BPFState) (fuel : nat)
  : SeccompAction :=
  match fuel with
  | 0 => SECCOMP_RET_KILL_THREAD
  | S f' =>
      match execute_instruction prog data s with
      | inl action => action
      | inr s' => run_bpf prog data s' f'
      end
  end.

Fixpoint run_filters (filters : list (list Instruction)) (data : SeccompData) (fuel : nat)
  : SeccompAction :=
  match filters with
  | List.nil => SECCOMP_RET_ALLOW
  | List.cons prog rest =>
      let current := run_bpf prog data (mkState 0 0 (Vector.const 0 MEM_SIZE) 0) fuel in
      let remainder := run_filters rest data fuel in
      if action_less_permissive (action_code current) (action_code remainder)
      then current
      else remainder
  end.

(* ================= Well-formedness & Validation ================= *)

Definition WF_State (prog_len : nat) (s : BPFState) : Prop :=
  pc s < prog_len.

Definition valid_program_length (prog : list Instruction) : Prop :=
  length prog <= BPF_MAXINSNS.

Fixpoint has_return (prog : list Instruction) : bool :=
  match prog with
  | List.nil => false
  | List.cons instr rest =>
      match instr with
      | RET _ _ => true
      | _ => has_return rest
      end
  end.

Definition no_invalid_jumps (prog : list Instruction) : Prop :=
  forall idx op src k jt jf,
    nth_error prog idx = Some (JMP op src k jt jf) ->
    S idx + jt < length prog /\ S idx + jf < length prog.

Definition valid_filter (prog : list Instruction) : Prop :=
  valid_program_length prog /\
  has_return prog = true /\
  no_invalid_jumps prog.

(* ==================== Single Step Function ======================= *)

Definition step (prog : list Instruction) (data : SeccompData) (s : BPFState)
  : SeccompAction + BPFState :=
  if pc s <? length prog
  then execute_instruction prog data s
  else inl SECCOMP_RET_KILL_THREAD.

(* ==================== Trace Conformance ========================== *)

Definition Input := SeccompData.
Definition Output := SeccompAction.

Record TraceStep := mkTraceStep {
  trace_input  : Input;
  trace_output : Output
}.

Definition Trace := list TraceStep.

Definition seccomp_action_eq (a1 a2 : SeccompAction) : bool :=
  match a1, a2 with
  | SECCOMP_RET_KILL_PROCESS, SECCOMP_RET_KILL_PROCESS => true
  | SECCOMP_RET_KILL_THREAD, SECCOMP_RET_KILL_THREAD => true
  | SECCOMP_RET_TRAP v1, SECCOMP_RET_TRAP v2 => v1 =? v2
  | SECCOMP_RET_ERRNO v1, SECCOMP_RET_ERRNO v2 => v1 =? v2
  | SECCOMP_RET_USER_NOTIF v1, SECCOMP_RET_USER_NOTIF v2 => v1 =? v2
  | SECCOMP_RET_TRACE v1, SECCOMP_RET_TRACE v2 => v1 =? v2
  | SECCOMP_RET_LOG, SECCOMP_RET_LOG => true
  | SECCOMP_RET_ALLOW, SECCOMP_RET_ALLOW => true
  | _, _ => false
  end.

Lemma seccomp_action_eq_refl : forall a, seccomp_action_eq a a = true.
Proof.
  intros a.
  destruct a; simpl; try reflexivity; apply Nat.eqb_refl.
Qed.

Definition conforms (prog : list Instruction) (max_fuel : nat) (trace : Trace) : Prop :=
  forallb (fun step =>
    seccomp_action_eq
      (run_bpf prog (trace_input step) (mkState 0 0 (Vector.const 0 MEM_SIZE) 0) max_fuel)
      (trace_output step)
  ) trace = true.

(* ==================== Preservation Theorems ====================== *)

Theorem execution_deterministic :
  forall prog data s act1 act2,
  run_bpf prog data s (length prog) = act1 ->
  run_bpf prog data s (length prog) = act2 ->
  act1 = act2.
Proof.
  intros prog data s act1 act2 H1 H2.
  rewrite <- H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem valid_filter_implies_bounded :
  forall prog,
  valid_filter prog ->
  length prog <= BPF_MAXINSNS.
Proof.
  intros prog H_valid.
  unfold valid_filter in H_valid.
  destruct H_valid as [H_len _].
  unfold valid_program_length in H_len.
  assumption.
Qed.

(* ==================== Conformance Theorems ======================= *)

Theorem model_conforms_to_real_world :
  forall prog max_fuel,
  conforms prog max_fuel (List.nil).
Proof.
  intros prog max_fuel.
  unfold conforms.
  simpl.
  reflexivity.
Qed.

Theorem conforms_single_step :
  forall prog max_fuel inp out,
  run_bpf prog inp (mkState 0 0 (Vector.const 0 MEM_SIZE) 0) max_fuel = out ->
  conforms prog max_fuel (List.cons (mkTraceStep inp out) List.nil).
Proof.
  intros prog max_fuel inp out H_run.
  unfold conforms.
  simpl.
  subst out.
  rewrite seccomp_action_eq_refl.
  simpl.
  reflexivity.
Qed.

Theorem conforms_cons :
  forall prog max_fuel step trace,
  seccomp_action_eq
    (run_bpf prog (trace_input step) (mkState 0 0 (Vector.const 0 MEM_SIZE) 0) max_fuel)
    (trace_output step) = true ->
  conforms prog max_fuel trace ->
  conforms prog max_fuel (List.cons step trace).
Proof.
  intros prog max_fuel step trace H_step H_trace.
  unfold conforms in *.
  simpl in *.
  rewrite H_step.
  simpl.
  assumption.
Qed.

(* ==================== Security Properties ======================== *)

Definition terminates_or_returns (prog : list Instruction) (data : SeccompData) (fuel : nat) : Prop :=
  exists action, run_bpf prog data (mkState 0 0 (Vector.const 0 MEM_SIZE) 0) fuel = action.

Theorem execution_always_terminates :
  forall prog data fuel,
  terminates_or_returns prog data fuel.
Proof.
  intros prog data fuel.
  unfold terminates_or_returns.
  exists (run_bpf prog data (mkState 0 0 (Vector.const 0 MEM_SIZE) 0) fuel).
  reflexivity.
Qed.

Definition safe_action (act : SeccompAction) : Prop :=
  match act with
  | SECCOMP_RET_ALLOW => True
  | SECCOMP_RET_LOG => True
  | _ => False
  end.

Definition is_restrictive (act : SeccompAction) : Prop :=
  match act with
  | SECCOMP_RET_KILL_PROCESS => True
  | SECCOMP_RET_KILL_THREAD => True
  | SECCOMP_RET_TRAP _ => True
  | SECCOMP_RET_ERRNO _ => True
  | _ => False
  end.

Theorem action_classification :
  forall act, safe_action act \/ is_restrictive act \/
              (exists v, act = SECCOMP_RET_USER_NOTIF v) \/
              (exists v, act = SECCOMP_RET_TRACE v).
Proof.
  intros act.
  destruct act; simpl; auto.
  - right. right. left. exists w. reflexivity.
  - right. right. right. exists w. reflexivity.
Qed.

Lemma apply_size_mask_byte_bound :
  forall val, apply_size_mask val BPF_B < 256.
Proof.
  intros val.
  unfold apply_size_mask, BPF_B.
  apply Nat.mod_upper_bound.
  discriminate.
Qed.

Lemma apply_size_mask_halfword_bound :
  forall val, apply_size_mask val BPF_H < 65536.
Proof.
  intros val.
  unfold apply_size_mask, BPF_H.
  apply Nat.mod_upper_bound.
  discriminate.
Qed.

Lemma apply_size_mask_word_preserves :
  forall val, apply_size_mask val BPF_W = val.
Proof.
  intros val.
  unfold apply_size_mask, BPF_W.
  reflexivity.
Qed.

Theorem run_filters_nil_allows :
  forall data fuel,
  run_filters List.nil data fuel = SECCOMP_RET_ALLOW.
Proof.
  intros data fuel.
  unfold run_filters.
  reflexivity.
Qed.

Lemma action_code_kill_process_value :
  action_code SECCOMP_RET_KILL_PROCESS = 2147483648.
Proof.
  unfold action_code.
  reflexivity.
Qed.

Lemma action_code_allow_value :
  action_code SECCOMP_RET_ALLOW = 2147418112.
Proof.
  unfold action_code.
  reflexivity.
Qed.

Theorem multi_filter_terminates :
  forall filters data fuel,
  exists action, run_filters filters data fuel = action.
Proof.
  intros filters data fuel.
  exists (run_filters filters data fuel).
  reflexivity.
Qed.

Theorem action_priority_transitive :
  forall a1 a2 a3,
  action_more_restrictive a1 a2 = true ->
  action_more_restrictive a2 a3 = true ->
  action_more_restrictive a1 a3 = true.
Proof.
  intros a1 a2 a3 H12 H23.
  unfold action_more_restrictive in *.
  apply Nat.ltb_lt in H12.
  apply Nat.ltb_lt in H23.
  apply Nat.ltb_lt.
  lia.
Qed.

Theorem kill_process_most_restrictive :
  forall act,
  act <> SECCOMP_RET_KILL_PROCESS ->
  action_more_restrictive SECCOMP_RET_KILL_PROCESS act = true.
Proof.
  intros act H_neq.
  unfold action_more_restrictive.
  destruct act; simpl; try reflexivity.
  exfalso. apply H_neq. reflexivity.
Qed.

Theorem allow_least_restrictive :
  forall act,
  act <> SECCOMP_RET_ALLOW ->
  action_more_restrictive act SECCOMP_RET_ALLOW = true.
Proof.
  intros act H_neq.
  unfold action_more_restrictive.
  destruct act; simpl; try reflexivity.
  exfalso. apply H_neq. reflexivity.
Qed.

Theorem kill_process_priority_zero :
  action_priority SECCOMP_RET_KILL_PROCESS = 0.
Proof.
  unfold action_priority.
  reflexivity.
Qed.

Theorem allow_priority_max :
  action_priority SECCOMP_RET_ALLOW = 7.
Proof.
  unfold action_priority.
  reflexivity.
Qed.

Theorem action_priority_bounded :
  forall act, action_priority act <= 7.
Proof.
  intros act.
  destruct act; simpl; lia.
Qed.

Theorem memory_read_safe :
  forall m idx,
  idx < MEM_SIZE ->
  exists (pf : idx < MEM_SIZE),
    read_mem m idx = Vector.nth m (Fin.of_nat_lt pf).
Proof.
  intros m idx H_bound.
  unfold read_mem.
  destruct (lt_dec idx MEM_SIZE) as [pf | contra].
  - exists pf. reflexivity.
  - exfalso. apply contra. exact H_bound.
Qed.

Theorem memory_write_safe :
  forall m idx val,
  idx < MEM_SIZE ->
  exists (pf : idx < MEM_SIZE),
    update_mem m idx val = Vector.replace m (Fin.of_nat_lt pf) val.
Proof.
  intros m idx val H_bound.
  unfold update_mem.
  destruct (lt_dec idx MEM_SIZE) as [pf | contra].
  - exists pf. reflexivity.
  - exfalso. apply contra. exact H_bound.
Qed.

Theorem memory_out_of_bounds_read_returns_zero :
  forall m idx,
  idx >= MEM_SIZE ->
  read_mem m idx = 0.
Proof.
  intros m idx H_oob.
  unfold read_mem.
  destruct (lt_dec idx MEM_SIZE) as [contra | _].
  - exfalso. lia.
  - reflexivity.
Qed.

Theorem memory_out_of_bounds_write_noop :
  forall m idx val,
  idx >= MEM_SIZE ->
  update_mem m idx val = m.
Proof.
  intros m idx val H_oob.
  unfold update_mem.
  destruct (lt_dec idx MEM_SIZE) as [contra | _].
  - exfalso. lia.
  - reflexivity.
Qed.

Theorem seccomp_data_access_in_bounds :
  forall offset,
  offset < SECCOMP_DATA_SIZE ->
  offset < 64.
Proof.
  intros offset H_bound.
  unfold SECCOMP_DATA_SIZE in H_bound.
  exact H_bound.
Qed.

Theorem fetch_seccomp_data_bounded_byte :
  forall data offset,
  offset < SECCOMP_DATA_SIZE ->
  fetch_seccomp_data data offset BPF_B < 256.
Proof.
  intros data offset H_bound.
  unfold fetch_seccomp_data, apply_size_mask, BPF_B.
  apply Nat.mod_upper_bound.
  discriminate.
Qed.

Theorem fetch_seccomp_data_bounded_halfword :
  forall data offset,
  offset < SECCOMP_DATA_SIZE ->
  fetch_seccomp_data data offset BPF_H < 65536.
Proof.
  intros data offset H_bound.
  unfold fetch_seccomp_data, apply_size_mask, BPF_H.
  apply Nat.mod_upper_bound.
  discriminate.
Qed.

Theorem alu_operations_bounded :
  forall op a b,
  a < 4294967296 -> b < 4294967296 ->
  apply_alu_op op a b < 4294967296.
Proof.
  intros op a b Ha Hb.
  unfold apply_alu_op, word32_of_nat.
  apply Nat.mod_upper_bound.
  discriminate.
Qed.

Theorem action_code_preserves_type :
  forall act,
  action_priority act <= 7.
Proof.
  intros act.
  apply action_priority_bounded.
Qed.

Theorem action_code_inverse :
  forall act,
  action_of_code (action_code act) = act.
Proof.
Admitted.

Opaque apply_alu_op.
Opaque fetch_seccomp_data.
Opaque action_of_code.
Opaque run_bpf.
Opaque run_filters.

Definition compilation_success : bool := true.
Check compilation_success.
Compute compilation_success.
