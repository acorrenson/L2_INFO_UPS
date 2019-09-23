----------------------------
-- Multiplexer 4 vers 1
----------------------------


library ieee;
use ieee.std_logic_1164.all;

-- entitee multiplexeur 4 vers 1
entity mux4_1 is
  port (
    input_signals : in std_logic_vector(3 downto 0);
    select_signal : in std_logic_vector(1 downto 0);
    output_signal : out std_logic
  );
end mux4_1;

-- architecture "data flow"
architecture mux4_1_df of mux4_1 is
  
  -- on utilise des multiplexexeurs 
  -- 2 vers 1 en composants internes.
  component mux2_1
  port (
    input_signals : in std_logic_vector(1 downto 0);
    select_signal : in std_logic;
    output_signal : out std_logic
  );
  end component;

  -- 2 sorties intermediaires
  -- pour 2 multiplexeurs 2 vers 1.
  signal output_mux2_1_A : std_logic;
  signal output_mux2_1_B : std_logic;

begin
  -- instance A de mux2_1
  mux2_1_A : mux2_1 port map (
    input_signals(0)  => input_signals(0),
    input_signals(1)  => input_signals(1),
    select_signal     => select_signal(0),
    output_signal     => output_mux2_1_A
  );

  -- instance B de mux2_1
  mux2_1_B : mux2_1 port map (
    input_signals(0)  => input_signals(2),
    input_signals(1)  => input_signals(3),
    select_signal     => select_signal(0),
    output_signal     => output_mux2_1_B
  );

  -- instance C de mux2_1
  mux2_1_C : mux2_1 port map (
    input_signals(0)  => output_mux2_1_A,
    input_signals(1)  => output_mux2_1_B,
    select_signal     => select_signal(1),
    output_signal     => output_signal
  );
end mux4_1_df;