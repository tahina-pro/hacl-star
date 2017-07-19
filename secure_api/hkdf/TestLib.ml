open FStar_Seq_Base

module Ansi = struct
  let mkcolor x = Printf.sprintf "\x1b[38;5;%dm" x

  let green = mkcolor 119
  let red = mkcolor 203
  let blue = mkcolor 81
  let yellow = mkcolor 227
  let orange = mkcolor 202
  let underline = "\x1b[4m"
  let reset = "\x1b[0m"
end


type uint8_p = FStar_UInt8.t seq

let uint8_p_to_string b len : string =
  let s = ref ""  in
  for i = 0 to len - 1 do
    s := !s ^ Printf.sprintf "%02x" (index b (Z.of_int i))
  done;
  !s

let compare_and_print (label:string) (expected:uint8_p) (computed:uint8_p) =
  let len = length expected |> Z.to_int in
  let expected_string = uint8_p_to_string expected len in
  let computed_string = uint8_p_to_string computed len in
  Printf.printf "[test] Expected: %s\n" expected_string;
  Printf.printf "[test] Computed: %s\n" computed_string;
  for i = 0 to 2 * len - 1 do
    if String.get expected_string i <> String.get computed_string i then
      begin
      Printf.printf "[test] Expected and computed differ at byte %d\n" (i/2 + 1);
      Printf.printf "[test] %s: %sFAIL%s\n" label Ansi.red Ansi.reset;
      failwith "Test failed"
      end
  done;
  Printf.printf "[test] %s: %sSUCCESS%s\n" label Ansi.green Ansi.reset
