----------------------------
-- Multiplexeur 2 vers 1
----------------------------


library ieee;
use ieee.std_logic_1164.all;

-- entitee multiplexeur 2 vers 1
entity mux2_1 is
  port (
    input_signals : in std_logic_vector(1 downto 0);
    select_signal : in std_logic;
    output_signal : out std_logic
  );
end mux2_1;

-- architecture "data flow"
architecture mux2_1_df of mux2_1 is
begin
  with select_signal select
    output_signal <=
      -- on selectionne l'entree 0
      input_signals(0) when '0',
      -- on selectionne l'entree 1
      input_signals(1) when '1',
      -- comportement non definis
      'X' when others;
end mux2_1_df;
