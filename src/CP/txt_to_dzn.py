def txt_to_dzn(FILE_DATA_URL):
    with open(FILE_DATA_URL) as f:
        txt_lines = f.readlines()
        f.close()

    dzn_lines = ['' for _ in range(len(txt_lines))]

    # print width
    dzn_lines[0] = 'width = ' + txt_lines[0][:-1] + ';\n'

    # print n_plates
    dzn_lines[1] = 'n_plates = ' + txt_lines[1][:-1] + ';\n'

    # print dims
    dzn_lines[2] = 'dims = ['
    for line_idx in range(2,len(txt_lines)):
        x, y = txt_lines[line_idx][:-1].split(sep=' ')
        dzn_lines[line_idx] += '|' + x + ', ' + y + ',\n'

    # remove last comma
    dzn_lines[-1] = dzn_lines[-1][:-1]

    # close the array
    dzn_lines[-1] += '|]'

    # save file
    FILE_DATA_URL_DZN = "data/input/dzn/ins-1.dzn"
    with open(FILE_DATA_URL_DZN, 'w') as f:
        f.writelines(dzn_lines)
        f.close()

    return FILE_DATA_URL_DZN