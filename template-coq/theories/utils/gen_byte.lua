
-- Small functions to generate Code for each byte constructor

function for_byte(fn)
    for i=0, 255 do
        fn(i, string.format("%02x", i))
    end
end

function generate_to_i63()
    for_byte(function(i, hex) 
        if i == 255 then
            io.write(string.format(" | x%s => 0x%s\n", hex, hex))
        elseif i % 4 == 0 then
            io.write(string.format("\n\t| x%s => 0x%s", hex, hex))
        else
            io.write(string.format(" | x%s => 0x%s", hex, hex))
        end
    end)
end

function generate_from_i63_array()
    io.write("[|")
    for_byte(function(i, hex) 
        if i == 255 then
            io.write(string.format(" x%s | x00\n|]\n", hex))
        elseif i % 8 == 0 then
            io.write(string.format("\n\tx%s; ", hex))
        else
            io.write(string.format(" x%s;", hex))
        end
    end)
end